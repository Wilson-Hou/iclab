//############################################################################
//   2026 Fall IC Lab / Exercise Lab03 / ZUMA  -- version 2
//
//   Same algorithm / latency as version 1 (2 cycles when chain_num = 0,
//   2n+1 cycles otherwise), restructured to shorten the critical path:
//   * Every address / pointer value that the next state may need is computed
//     from registers in parallel with the ring read; the read result (run
//     lengths) only drives late multiplexer selects.
//   * The per-entry "i >= start" mask comes from one thermometer of the
//     register lp, shifted by the run length (lp+1 / lp / lp-1), instead of
//     comparing against an arithmetic result.
//   * Ring loading is written one cycle after in_valid (registered inputs),
//     removing the input -> 768-bit fan-out path.
//
//   Ring model (same as version 1)
//   * ring[i] = bead with logical index i, M = number of beads.
//   * Every same-color run is at most 2 beads, so a cascade level is decided
//     by 4 beads around the junction (a0=lp-1, lp | rp, a3=rp+1), and one
//     level deletes at most 4 beads (shift down by 1~4).
//   * EV1 : level 1. No elimination -> insert, output chain 0.
//           Elimination -> delete the matched old beads.
//     CNT : read-only walk (pointers move outward) to find chain_num.
//     OUT : output level 1, then levels 2..n while deleting them.
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
//   REG
//---------------------------------------------------------------------
reg  [1:0]   state;
reg  [2:0]   ring [0:255];
reg  [8:0]   M;                  // beads in the ring
reg  [8:0]   Mrem;               // beads remaining during the CNT walk
reg  [7:0]   lp, rp, a0, a3;     // junction, a0 = lp-1, a3 = rp+1 (mod M)
reg  [7:0]   lp1, rp1, a01, a31; // junction right after level 1
reg  [2:0]   c_r;                // shot color
reg  [6:0]   lv;                 // levels found
reg  [6:0]   rem_out;            // levels left to output
reg  [2:0]   cnt1;               // elim_cnt of level 1
reg          in_valid_d;
reg          ld_v, ld_first;     // registered loading inputs
reg  [2:0]   ld_c;

//---------------------------------------------------------------------
//   Values derived from registers only (early)
//---------------------------------------------------------------------
wire [8:0] Mm1 = M - 9'd1;
wire [8:0] Mm2 = M - 9'd2;
wire [8:0] Mm3 = M - 9'd3;
wire [8:0] Mm4 = M - 9'd4;
wire [8:0] Mm5 = M - 9'd5;
wire [8:0] Mm6 = M - 9'd6;
wire       emp = (M == 9'd0);

wire       is_l1 = (state == S_EV1);
wire       is_cnt = (state == S_CNT);
wire [8:0] Mx   = is_cnt ? Mrem : M;
wire       Mge4 = (Mx >= 9'd4);

wire       lp_is0   = (lp == 8'd0);
wire       lp_is1   = (lp == 8'd1);
wire       rp_is0   = (rp == 8'd0);
wire       rp_is1   = (rp == 8'd1);
wire       a0_is0   = (a0 == 8'd0);
wire       a0_is1   = (a0 == 8'd1);
wire       lp_isMm1 = ({1'b0, lp} == Mm1);
wire       rp_isMm1 = ({1'b0, rp} == Mm1);

wire [7:0] lm2 = a0_is0 ? Mm1[7:0] : (a0 - 8'd1);                 // lp-2 mod M
wire [7:0] lm3 = (lm2 == 8'd0) ? Mm1[7:0] : (lm2 - 8'd1);         // lp-3 mod M
wire [7:0] rp2 = ({1'b0, a3}  == Mm1) ? 8'd0 : (a3  + 8'd1);      // rp+2 mod M
wire [7:0] rp3 = ({1'b0, rp2} == Mm1) ? 8'd0 : (rp2 + 8'd1);      // rp+3 mod M
wire [8:0] rpp1 = {1'b0, rp} + 9'd1;
wire [8:0] lpp1 = {1'b0, lp} + 9'd1;

// thermometer of lp : T[i] = (i >= lp)
wire [256:0] T;
generate
for (g = 0; g < 256; g = g + 1) begin : G_T
    assign T[g] = (g >= lp);
end
endgenerate
assign T[256] = 1'b1;

//---------------------------------------------------------------------
//   Junction evaluation (ring read -> run lengths)
//---------------------------------------------------------------------
wire [2:0] rd_msk = {3{~emp}};     // entries are unknown when the ring is empty
wire [2:0] x0 = ring[a0] & rd_msk;
wire [2:0] x1 = ring[lp] & rd_msk;
wire [2:0] x2 = ring[rp] & rd_msk;
wire [2:0] x3 = ring[a3] & rd_msk;

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
wire [2:0] raw  = {1'b0, lenL} + {1'b0, lenR};
wire [2:0] tot  = (!Mge4 && (Mx[2:0] < raw)) ? Mx[2:0] : raw;   // beads removed
wire       elim = is_l1 ? (tot >= 3'd2) : (eqc && (tot >= 3'd3));

wire       L0 = (lenL == 2'd0);
wire       L1 = (lenL == 2'd1);
wire       L2 = (lenL == 2'd2);

//---------------------------------------------------------------------
//   Deletion of [st, st+tot) around the junction (EV1 / OUT)
//   st = lp+1-lenL, i.e. rp / lp / a0; three wrap cases cross M-1 -> 0.
//---------------------------------------------------------------------
wire       w_i   = lp_is0 & L2;                        // deletes M-1, 0, right run
wire       w_ii  = lp_isMm1 & ~L0 & (lenR != 2'd0);    // junction at M-1 | 0
wire       w_iii = rp_isMm1 & (lenR == 2'd2);          // deletes left run, M-1, 0
wire       wrp   = w_i | w_ii | w_iii;

wire [7:0] st_c  = L0 ? rp     : (L1 ? lp     : a0);
wire       st_c0 = L0 ? rp_is0 : (L1 ? lp_is0 : a0_is0);
wire       st_c1 = L0 ? rp_is1 : (L1 ? lp_is1 : a0_is1);
wire       st_zero = wrp | st_c0;                      // deletion starts at 0

reg  [2:0] sh;
always @(*) begin
    if (w_i)        sh = {1'b0, lenR} + 3'd1;
    else if (w_ii)  sh = {1'b0, lenR};
    else if (w_iii) sh = 3'd1;
    else            sh = tot;
end

reg  [8:0] Mp, Mpm1, Mpm2;         // M-tot, M-tot-1, M-tot-2
always @(*) begin
    case (tot)
        3'd2:    begin Mp = Mm2; Mpm1 = Mm3; Mpm2 = Mm4; end
        3'd3:    begin Mp = Mm3; Mpm1 = Mm4; Mpm2 = Mm5; end
        3'd4:    begin Mp = Mm4; Mpm1 = Mm5; Mpm2 = Mm6; end
        default: begin Mp = M - {6'd0, tot}; Mpm1 = Mp - 9'd1; Mpm2 = Mp - 9'd2; end
    endcase
end

wire       eqend = ({1'b0, st_c} == Mp);               // deletion reaches the end
wire       rz    = st_zero | eqend;
wire [8:0] stp1  = L0 ? rpp1 : (L1 ? lpp1 : {1'b0, lp});
wire [7:0] lp_n  = st_zero ? Mpm1[7:0] : (L0 ? lp : (L1 ? a0 : lm2));
wire [7:0] a0_n  = st_zero ? Mpm2[7:0] :
                   st_c1   ? Mpm1[7:0] : (L0 ? a0 : (L1 ? lm2 : lm3));
wire [7:0] rp_n  = rz ? 8'd0 : st_c;
wire [7:0] a3_n  = rz ? ((Mp == 9'd1) ? 8'd0 : 8'd1) :
                        ((stp1 == Mp) ? 8'd0 : stp1[7:0]);

//---------------------------------------------------------------------
//   Read-only walk (CNT)
//---------------------------------------------------------------------
wire [7:0] lp_w = L1 ? a0  : lm2;
wire [7:0] a0_w = L1 ? lm2 : lm3;
wire [7:0] rp_w = (lenR == 2'd1) ? a3  : rp2;
wire [7:0] a3_w = (lenR == 2'd1) ? rp2 : rp3;

//---------------------------------------------------------------------
//   Shot capture
//---------------------------------------------------------------------
wire       sp_isMm1 = ({1'b0, shot_pos} == Mm1);
wire       sp_isMm2 = ({1'b0, shot_pos} == Mm2);
wire [7:0] rp_s = sp_isMm1 ? 8'd0 : (shot_pos + 8'd1);
wire [7:0] a3_s = (M == 9'd1) ? 8'd0 : (sp_isMm2 ? 8'd0 : (sp_isMm1 ? 8'd1 : (shot_pos + 8'd2)));
wire [7:0] a0_s = (shot_pos == 8'd0) ? Mm1[7:0] : (shot_pos - 8'd1);

//---------------------------------------------------------------------
//   Ring update
//---------------------------------------------------------------------
wire       md_ins  = ld_v | (is_l1 & ~elim);
wire       md_del  = ~ld_v & ((is_l1 & elim) | ((state == S_OUT) && (rem_out != 7'd0)));
wire       ins_emp = ld_v ? ld_first : emp;            // insert at index 0
wire [2:0] cin     = ld_v ? ld_c : c_r;                // otherwise insert at lp+1

wire [767:0] cur;
generate
for (g = 0; g < 256; g = g + 1) begin : G_FLAT
    assign cur[3*g +: 3] = ring[g];
end
endgenerate

wire [767:0] up1 = {cur[764:0], 3'd0};                 // up1[i] = ring[i-1]
reg  [767:0] dsh;                                      // dsh[i] = ring[i+sh]
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
    wire tm2 = (g >= 2) ? T[(g >= 2) ? g-2 : 0] : 1'b0;   // i-2 >= lp
    wire tm1 = (g >= 1) ? T[(g >= 1) ? g-1 : 0] : 1'b0;   // i-1 >= lp
    wire t0  = T[g];                                      // i   >= lp
    wire tp1 = T[g+1];                                    // i+1 >= lp
    wire ge_ins = ins_emp | tm1;
    wire eq_ins = ins_emp ? (g == 0) : (tm1 & ~tm2);
    wire ge_del = st_zero | (L0 & tm1) | (L1 & t0) | (L2 & tp1);
    assign nxt[3*g +: 3] = md_del ? (ge_del ? dsh[3*g +: 3] : cur[3*g +: 3]) :
                           md_ins ? (ge_ins ? (eq_ins ? cin : up1[3*g +: 3]) : cur[3*g +: 3]) :
                                    cur[3*g +: 3];
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
        lv         <= 7'd0;
        rem_out    <= 7'd0;
        cnt1       <= 3'd0;
        in_valid_d <= 1'b0;
        ld_v       <= 1'b0;
        ld_first   <= 1'b0;
        ld_c       <= 3'd0;
        out_valid  <= 1'b0;
        chain_num  <= 7'd0;
        elim_color <= 3'd0;
        elim_cnt   <= 9'd0;
    end
    else begin
        in_valid_d <= in_valid;
        ld_v       <= in_valid;
        ld_first   <= in_valid & ~in_valid_d;
        ld_c       <= in_color;
        if (in_valid) begin
            state      <= S_IDLE;
            out_valid  <= 1'b0;
            chain_num  <= 7'd0;
            elim_color <= 3'd0;
            elim_cnt   <= 9'd0;
            if (ld_v) begin
                M  <= ld_first ? 9'd1 : (M + 9'd1);
                lp <= ld_first ? 8'd0 : lpp1[7:0];
            end
        end
        else if (ld_v) begin
            M  <= ld_first ? 9'd1 : (M + 9'd1);
            lp <= ld_first ? 8'd0 : lpp1[7:0];
        end
        else begin
            case (state)
            S_IDLE: begin
                if (shot_valid) begin
                    state <= S_EV1;
                    c_r   <= shot_color;
                    lp    <= shot_pos;
                    rp    <= rp_s;
                    a0    <= a0_s;
                    a3    <= a3_s;
                end
            end
            S_EV1: begin
                if (elim) begin
                    state <= S_CNT;
                    M     <= Mp;
                    Mrem  <= Mp;
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
                    M          <= Mp;
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
