//############################################################################
//   2026 Fall IC Lab / Exercise Lab03 / ZUMA
//
//   Architecture
//   ------------
//   * The ring is kept in a 256-entry color array, logical index i at entry i.
//   * Because the initial ring never contains a segment of 3+ beads and every
//     segment that reaches 3 is removed immediately, every same-color run in
//     the ring is at most 2 beads long. Hence a cascade level is fully decided
//     by the 4 beads around the current junction (lp-1, lp | rp, rp+1), and
//     one level removes at most 4 beads.
//   * Shot flow (one cascade level per cycle):
//       EV1 : evaluate level 1. No elimination -> insert bead, output chain 0.
//             Elimination -> delete the (<=4) matched old beads right away.
//       CNT : walk the remaining levels read-only (two pointers moving outward)
//             to find chain_num.
//       OUT : output level 1 (saved), then re-walk levels 2..n while
//             outputting them, deleting each level's beads (shift <= 4).
//     Latency per shot: 2 cycles when chain_num = 0, 2n+1 otherwise.
//############################################################################
module ZUMA (
    input               clk,
    input               rst_n,
    // ---- ring loading phase ----
    input               in_valid,
    input      [7:0]    ring_len,
    input      [2:0]    in_color,
    // ---- shooting phase ----
    input               shot_valid,
    input      [2:0]    shot_color,
    input      [7:0]    shot_pos,
    // ---- outputs ----
    output reg          out_valid,
    output reg [6:0]    chain_num,
    output reg [2:0]    elim_color,
    output reg [8:0]    elim_cnt
);

//---------------------------------------------------------------------
//   PARAMETER
//---------------------------------------------------------------------
localparam S_IDLE = 2'd0;
localparam S_EV1  = 2'd1;
localparam S_CNT  = 2'd2;
localparam S_OUT  = 2'd3;

integer k;
genvar  g;

//---------------------------------------------------------------------
//   REG & WIRE
//---------------------------------------------------------------------
reg  [1:0]   state;
reg  [2:0]   ring [0:255];
reg  [8:0]   M;                 // number of beads in the ring (0~256)
reg  [8:0]   Mrem;              // beads remaining during the read-only walk
reg  [7:0]   lp, rp, a0, a3;    // junction: a0 = lp-1, a3 = rp+1 (mod M)
reg  [7:0]   lp1, rp1, a01, a31;// junction right after level 1
reg  [2:0]   c_r;               // shot color
reg  [7:0]   ins_r;             // insertion index of the shot bead
reg  [6:0]   lv;                // number of levels found so far
reg  [6:0]   rem_out;           // levels left to output
reg  [2:0]   cnt1;              // elim_cnt of level 1
reg          in_valid_d;

//---------------------------------------------------------------------
//   Junction evaluation (shared by EV1 / CNT / OUT)
//---------------------------------------------------------------------
// masked when the ring is empty (entries may be uninitialized)
wire [2:0] rd_msk = {3{(M != 9'd0)}};
wire [2:0] x0 = ring[a0] & rd_msk;
wire [2:0] x1 = ring[lp] & rd_msk;
wire [2:0] x2 = ring[rp] & rd_msk;
wire [2:0] x3 = ring[a3] & rd_msk;

wire       is_l1 = (state == S_EV1);

// level 1 : beads equal to the shot color on each side of the insert point
wire       m1 = (x1 == c_r);
wire       m0 = m1 & (x0 == c_r);
wire       m2 = (x2 == c_r);
wire       m3 = m2 & (x3 == c_r);
wire [1:0] cl = {m0, m1 & ~m0};
wire [1:0] cr = {m3, m2 & ~m3};

// level >= 2 : the two runs meeting at the junction
wire       eqc = (x1 == x2);
wire [1:0] kl  = (x0 == x1) ? 2'd2 : 2'd1;
wire [1:0] kr  = (x3 == x2) ? 2'd2 : 2'd1;

wire [1:0] lenL = is_l1 ? cl : kl;
wire [1:0] lenR = is_l1 ? cr : kr;
wire [2:0] raw  = lenL + lenR;
wire [8:0] Mx   = (state == S_CNT) ? Mrem : M;
wire [2:0] tot  = (Mx < {6'd0, raw}) ? Mx[2:0] : raw;   // old beads removed
wire       elim = is_l1 ? (tot >= 3'd2) : (eqc && (tot >= 3'd3));

//---------------------------------------------------------------------
//   Deletion of the eliminated beads (EV1 / OUT)
//---------------------------------------------------------------------
wire [7:0] a_st  = (lenL == 2'd0) ? rp : ((lenL == 2'd1) ? lp : a0);
wire [9:0] a_sum = {2'd0, a_st} + {7'd0, tot};
wire       wrp   = (a_sum > {1'b0, M});
wire [9:0] a_ovf = a_sum - {1'b0, M};
wire [2:0] sh    = wrp ? a_ovf[2:0] : tot;
wire [7:0] st    = wrp ? 8'd0 : a_st;
wire [8:0] Mn    = M - {6'd0, tot};
wire [8:0] Mn_m1 = Mn - 9'd1;
wire [7:0] lp_n  = (st == 8'd0) ? Mn_m1[7:0] : (st - 8'd1);
wire [7:0] rp_n  = ({1'b0, st} == Mn) ? 8'd0 : st;
wire [7:0] a0_n  = (lp_n == 8'd0) ? Mn_m1[7:0] : (lp_n - 8'd1);
wire [8:0] rp_n1 = {1'b0, rp_n} + 9'd1;
wire [7:0] a3_n  = (rp_n1 == Mn) ? 8'd0 : rp_n1[7:0];

//---------------------------------------------------------------------
//   Read-only walk (CNT): pointers move outward, mod M
//---------------------------------------------------------------------
wire [9:0] lw_t  = {2'd0, lp} - {8'd0, lenL};
wire [9:0] lw_a  = lw_t + {1'b0, M};
wire [7:0] lp_w  = lw_t[9] ? lw_a[7:0] : lw_t[7:0];
wire [8:0] M_m1  = M - 9'd1;
wire [7:0] a0_w  = (lp_w == 8'd0) ? M_m1[7:0] : (lp_w - 8'd1);
wire [9:0] rw_t  = {2'd0, rp} + {8'd0, lenR};
wire [9:0] rw_s  = rw_t - {1'b0, M};
wire [7:0] rp_w  = (rw_t >= {1'b0, M}) ? rw_s[7:0] : rw_t[7:0];
wire [8:0] rp_w1 = {1'b0, rp_w} + 9'd1;
wire [7:0] a3_w  = (rp_w1 == M) ? 8'd0 : rp_w1[7:0];

//---------------------------------------------------------------------
//   Shot capture: pointers around the insert point
//---------------------------------------------------------------------
wire [8:0] sp1   = {1'b0, shot_pos} + 9'd1;
wire [7:0] rp_s  = (sp1 == M) ? 8'd0 : sp1[7:0];
wire [8:0] rp_s1 = {1'b0, rp_s} + 9'd1;
wire [7:0] a3_s  = (rp_s1 == M) ? 8'd0 : rp_s1[7:0];
wire [7:0] a0_s  = (shot_pos == 8'd0) ? M_m1[7:0] : (shot_pos - 8'd1);

//---------------------------------------------------------------------
//   Ring update: hold / insert one bead / delete (shift down by sh)
//---------------------------------------------------------------------
reg        md_ins, md_del;
reg  [7:0] idx;
reg  [2:0] cin;

always @(*) begin
    md_ins = 1'b0;
    md_del = 1'b0;
    idx    = st;
    cin    = c_r;
    if (in_valid) begin
        md_ins = 1'b1;
        idx    = in_valid_d ? M[7:0] : 8'd0;
        cin    = in_color;
    end
    else if (state == S_EV1) begin
        if (elim) begin
            md_del = 1'b1;
        end
        else begin
            md_ins = 1'b1;
            idx    = ins_r;
        end
    end
    else if (state == S_OUT && rem_out != 7'd0) begin
        md_del = 1'b1;
    end
end

wire [767:0] cur;
generate
for (g = 0; g < 256; g = g + 1) begin : G_FLAT
    assign cur[3*g +: 3] = ring[g];
end
endgenerate

wire [767:0] up1 = {cur[764:0], 3'd0};      // up1[i] = ring[i-1]
reg  [767:0] dsh;                           // dsh[i] = ring[i+sh]
always @(*) begin
    case (sh)
        3'd1:    dsh = {3'd0,  cur[767:3]};
        3'd2:    dsh = {6'd0,  cur[767:6]};
        3'd3:    dsh = {9'd0,  cur[767:9]};
        default: dsh = {12'd0, cur[767:12]};
    endcase
end

wire [767:0] nxt;
generate
for (g = 0; g < 256; g = g + 1) begin : G_NXT
    wire ge = (g >= idx);
    wire eq = (g == idx);
    assign nxt[3*g +: 3] = (!ge || (!md_ins && !md_del)) ? cur[3*g +: 3] :
                           md_ins ? (eq ? cin : up1[3*g +: 3]) :
                                    dsh[3*g +: 3];
end
endgenerate

always @(posedge clk) begin
    for (k = 0; k < 256; k = k + 1)
        ring[k] <= nxt[3*k +: 3];
end

//---------------------------------------------------------------------
//   Control
//---------------------------------------------------------------------
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state      <= S_IDLE;
        M          <= 9'd0;
        Mrem       <= 9'd0;
        lp         <= 8'd0;
        rp         <= 8'd0;
        a0         <= 8'd0;
        a3         <= 8'd0;
        lp1        <= 8'd0;
        rp1        <= 8'd0;
        a01        <= 8'd0;
        a31        <= 8'd0;
        c_r        <= 3'd0;
        ins_r      <= 8'd0;
        lv         <= 7'd0;
        rem_out    <= 7'd0;
        cnt1       <= 3'd0;
        in_valid_d <= 1'b0;
        out_valid  <= 1'b0;
        chain_num  <= 7'd0;
        elim_color <= 3'd0;
        elim_cnt   <= 9'd0;
    end
    else begin
        in_valid_d <= in_valid;
        if (in_valid) begin
            state      <= S_IDLE;
            M          <= in_valid_d ? (M + 9'd1) : 9'd1;
            out_valid  <= 1'b0;
            chain_num  <= 7'd0;
            elim_color <= 3'd0;
            elim_cnt   <= 9'd0;
        end
        else begin
            case (state)
            S_IDLE: begin
                if (shot_valid) begin
                    state <= S_EV1;
                    c_r   <= shot_color;
                    ins_r <= (M == 9'd0) ? 8'd0 : sp1[7:0];
                    lp    <= shot_pos;
                    rp    <= rp_s;
                    a0    <= a0_s;
                    a3    <= a3_s;
                end
            end
            S_EV1: begin
                if (elim) begin
                    state <= S_CNT;
                    M     <= Mn;
                    Mrem  <= Mn;
                    lp    <= lp_n;
                    rp    <= rp_n;
                    a0    <= a0_n;
                    a3    <= a3_n;
                    lp1   <= lp_n;
                    rp1   <= rp_n;
                    a01   <= a0_n;
                    a31   <= a3_n;
                    lv    <= 7'd1;
                    cnt1  <= tot + 3'd1;
                end
                else begin
                    state      <= S_OUT;
                    M          <= M + 9'd1;
                    rem_out    <= 7'd0;
                    out_valid  <= 1'b1;
                    chain_num  <= 7'd0;
                    elim_color <= 3'd0;
                    elim_cnt   <= 9'd0;
                end
            end
            S_CNT: begin
                if (elim) begin
                    lv   <= lv + 7'd1;
                    Mrem <= Mrem - {6'd0, tot};
                    lp   <= lp_w;
                    rp   <= rp_w;
                    a0   <= a0_w;
                    a3   <= a3_w;
                end
                else begin
                    state      <= S_OUT;
                    rem_out    <= lv - 7'd1;
                    lp         <= lp1;
                    rp         <= rp1;
                    a0         <= a01;
                    a3         <= a31;
                    out_valid  <= 1'b1;
                    chain_num  <= lv;
                    elim_color <= c_r;
                    elim_cnt   <= {6'd0, cnt1};
                end
            end
            default: begin // S_OUT
                if (rem_out != 7'd0) begin
                    rem_out    <= rem_out - 7'd1;
                    M          <= Mn;
                    lp         <= lp_n;
                    rp         <= rp_n;
                    a0         <= a0_n;
                    a3         <= a3_n;
                    elim_color <= x1;
                    elim_cnt   <= {6'd0, tot};
                end
                else begin
                    state      <= S_IDLE;
                    out_valid  <= 1'b0;
                    chain_num  <= 7'd0;
                    elim_color <= 3'd0;
                    elim_cnt   <= 9'd0;
                end
            end
            endcase
        end
    end
end

endmodule
