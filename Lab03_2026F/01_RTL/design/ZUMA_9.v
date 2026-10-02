//############################################################################
//   2026 Fall IC Lab / Exercise Lab03 / ZUMA  -- version 9
//
//   Latency per shot : 2 cycles when chain_num = 0, 2n cycles otherwise.
//
//   Ring model
//   * ring[i] = bead with logical index i, M = number of beads.
//   * Every same-color run is at most 2 beads, so a cascade level is decided
//     by 4 beads around the junction and one level deletes at most 4 beads.
//
//   Reads : two 4-entry windows instead of single-entry ports.
//     WL = lp-3 .. lp  (left of the junction),  WR = rp .. rp+3 (right).
//     Each window is read from an even / odd block bank (4 entries per
//     block): a 4-entry window always spans one even and one odd block, so a
//     window costs about as much as a single 256:1 read port.
//     Entries past M-1 wrap to ring[0..2].
//     The windows hold the current level (lp-1, lp | rp, rp+1) and the next
//     one, so the level after the current one is known one cycle earlier.
//
//   Flow
//     EV1 : level 1 (+ look-ahead of level 2).
//           no elimination   -> insert the bead, output chain 0.
//           level 1 only     -> delete level 1, output chain 1 now.
//           level 2 as well  -> delete level 1, go to CNT.
//     CNT : read-only walk over levels 2.. with look-ahead, finds chain_num.
//     OUT : output level 1, then levels 2..n while deleting them.
//
//   Version 9: original banked window and mutually exclusive ring-write enables.
//   Area refinement over version 3
//     After level 1 is physically deleted, the two junction beads are
//     adjacent.  Therefore rp1 and wsl1 are functions of lp1 and M; only lp1
//     is retained across the read-only CNT walk.  This removes 16 flip-flops
//     without adding logic to the window-read critical path.
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
reg  [767:0] cur;
reg  [8:0]   M;                  // beads in the ring
reg  [8:0]   Mrem;               // beads remaining before the CNT level
reg  [7:0]   lp, rp;             // junction
reg  [7:0]   wsl;                // lp-3 (mod M), start of the left window
reg  [7:0]   lp1;                // left junction bead right after level 1
reg  [2:0]   c_r;                // shot color
reg  [6:0]   lv;                 // levels confirmed before the CNT level
reg  [6:0]   rem_out;            // levels left to output
reg  [2:0]   cnt1;               // elim_cnt of level 1
reg          in_valid_d;
reg          ld_v, ld_first;     // registered loading inputs
reg  [2:0]   ld_c;

//---------------------------------------------------------------------
//   Values derived from registers only
//---------------------------------------------------------------------
wire [8:0] Mm1 = M - 9'd1;
wire [8:0] Mm2 = M - 9'd2;
wire [8:0] Mm3 = M - 9'd3;
wire [8:0] Mm4 = M - 9'd4;
wire [8:0] Mm5 = M - 9'd5;
wire [8:0] Mm6 = M - 9'd6;
wire [8:0] Mm7 = M - 9'd7;
wire [8:0] Mm8 = M - 9'd8;
wire       emp  = (M == 9'd0);
wire       M_is1 = (M == 9'd1);
wire       M_is2 = (M == 9'd2);

wire       is_l1  = (state == S_EV1);
wire       is_cnt = (state == S_CNT);
wire [8:0] Mx   = is_cnt ? Mrem : M;
wire       Mge4 = (Mx >= 9'd4);

wire       lp_is0   = (lp == 8'd0);
wire       lp_isMm1 = ({1'b0, lp} == Mm1);
wire       rp_isMm1 = ({1'b0, rp} == Mm1);
wire [7:0] a0   = lp_is0 ? Mm1[7:0] : (lp - 8'd1);                 // lp-1
wire       a0_is0 = (a0 == 8'd0);
wire [7:0] lm2  = a0_is0 ? Mm1[7:0] : (a0 - 8'd1);                 // lp-2
wire [7:0] a3   = rp_isMm1 ? 8'd0 : (rp + 8'd1);                   // rp+1
wire [7:0] rp2  = ({1'b0, a3} == Mm1) ? 8'd0 : (a3 + 8'd1);        // rp+2
wire [7:0] wm1  = (wsl == 8'd0) ? Mm1[7:0] : (wsl - 8'd1);         // lp-4
wire [7:0] wm2  = (wm1 == 8'd0) ? Mm1[7:0] : (wm1 - 8'd1);         // lp-5
wire       rp_is0 = (rp == 8'd0);
wire       lp_ge3  = (lp  >= 8'd3);
wire       a0_ge3  = (a0  >= 8'd3);
wire       lm2_ge3 = (lm2 >= 8'd3);
wire [8:0] lpp1 = {1'b0, lp} + 9'd1;

// Restore the compacted level-1 junction after the read-only CNT walk.
// M is the physical ring length after level 1 throughout S_CNT.
wire [7:0] rp1_restore = ({1'b0, lp1} == Mm1) ? 8'd0 : (lp1 + 8'd1);
wire [8:0] lp1_plus_M  = {1'b0, lp1} + M;
wire [7:0] wsl1_restore = (lp1 >= 8'd3) ? (lp1 - 8'd3) :
                           (lp1_plus_M - 9'd3);

// thermometer of lp : T[i] = (i >= lp)
wire [256:0] T;
generate
for (g = 0; g < 256; g = g + 1) begin : G_T
    assign T[g] = (g >= lp);
end
endgenerate
assign T[256] = 1'b1;

//---------------------------------------------------------------------
//   Window reads
//---------------------------------------------------------------------
// Flat storage preserves the 256 logical entries without array event overhead.

wire [11:0] wl_raw, wr_raw;
ZUMA_WIN u_wl (.cur(cur), .st(wsl), .win(wl_raw));
ZUMA_WIN u_wr (.cur(cur), .st(rp),  .win(wr_raw));

// wrap past M-1 to ring[0..2], exact mod M for M = 1 / 2
wire [2:0] r0 = cur[2:0];
wire [2:0] r1 = cur[5:3];
wire [2:0] r2 = cur[8:6];
wire [2:0] WL [0:3];
wire [2:0] WR [0:3];
generate
for (g = 0; g < 4; g = g + 1) begin : G_FIX
    wire [8:0] tl  = {1'b0, wsl} + g;
    wire [8:0] tr  = {1'b0, rp}  + g;
    wire [1:0] dl  = tl[1:0] - M[1:0];                 // tl-M (0..2) when tl >= M
    wire [1:0] dr  = tr[1:0] - M[1:0];
    wire [2:0] hl  = (dl == 2'd0) ? r0 : ((dl == 2'd1) ? r1 : r2);
    wire [2:0] hr  = (dr == 2'd0) ? r0 : ((dr == 2'd1) ? r1 : r2);
    wire       pl2 = lp[0] ^ ((g % 2) == 1);                     // (lp+g+1) mod 2 == 0
    wire       pr2 = rp[0] ^ ((g % 2) == 1);                     // (rp+g) mod 2
    assign WL[g] = emp   ? 3'd0 :
                   M_is1 ? r0 :
                   M_is2 ? (pl2 ? r0 : r1) :
                   (tl >= M) ? hl : wl_raw[3*g +: 3];
    assign WR[g] = emp   ? 3'd0 :
                   M_is1 ? r0 :
                   M_is2 ? (pr2 ? r1 : r0) :
                   (tr >= M) ? hr : wr_raw[3*g +: 3];
end
endgenerate

//---------------------------------------------------------------------
//   Current level
//---------------------------------------------------------------------
wire [2:0] x0 = WL[2];
wire [2:0] x1 = WL[3];
wire [2:0] x2 = WR[0];
wire [2:0] x3 = WR[1];

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
//   Look-ahead : the level after the current one
//---------------------------------------------------------------------
wire [2:0] y1 = L0 ? WL[3] : (L1 ? WL[2] : WL[1]);
wire [2:0] y0 = L0 ? WL[2] : (L1 ? WL[1] : WL[0]);
wire [2:0] y2 = (lenR == 2'd0) ? WR[0] : ((lenR == 2'd1) ? WR[1] : WR[2]);
wire [2:0] y3 = (lenR == 2'd0) ? WR[1] : ((lenR == 2'd1) ? WR[2] : WR[3]);
wire [8:0] Mr2   = Mx - {6'd0, tot};
reg        Mr2ge3;                                     // Mx - tot >= 3
always @(*) begin
    case (tot)
        3'd0:    Mr2ge3 = (Mx >= 9'd3);
        3'd1:    Mr2ge3 = (Mx >= 9'd4);
        3'd2:    Mr2ge3 = (Mx >= 9'd5);
        3'd3:    Mr2ge3 = (Mx >= 9'd6);
        default: Mr2ge3 = (Mx >= 9'd7);
    endcase
end
wire       elim2 = (y1 == y2) && Mr2ge3 && ((y0 == y1) || (y3 == y2));

//---------------------------------------------------------------------
//   Deletion of [st, st+tot) around the junction (EV1 / OUT)
//---------------------------------------------------------------------
wire       w_i   = lp_is0 & L2;                        // deletes M-1, 0, right run
wire       w_ii  = lp_isMm1 & ~L0 & (lenR != 2'd0);    // junction at M-1 | 0
wire       w_iii = rp_isMm1 & (lenR == 2'd2);          // deletes left run, M-1, 0
wire       wrp   = w_i | w_ii | w_iii;

wire [7:0] st_c  = L0 ? rp     : (L1 ? lp     : a0);
wire       st_c0 = L0 ? rp_is0 : (L1 ? lp_is0 : a0_is0);
wire       st_zero = wrp | st_c0;                      // deletion starts at 0

reg  [2:0] sh;
always @(*) begin
    if (w_i)        sh = {1'b0, lenR} + 3'd1;
    else if (w_ii)  sh = {1'b0, lenR};
    else if (w_iii) sh = 3'd1;
    else            sh = tot;
end

// every candidate below is computed from registers; tot / lenL only select
reg  [8:0] Mp, Mpm1, Mpm4;         // M' = M-tot, M'-1, M'-4
reg        Mpge4;                  // M' >= 4
reg        eq_rp, eq_lp, eq_a0;    // rp / lp / a0 == M'
always @(*) begin
    case (tot)
        3'd2: begin
            Mp = Mm2; Mpm1 = Mm3; Mpm4 = Mm6; Mpge4 = (M >= 9'd6);
            eq_rp = ({1'b0, rp} == Mm2); eq_lp = ({1'b0, lp} == Mm2); eq_a0 = ({1'b0, a0} == Mm2);
        end
        3'd3: begin
            Mp = Mm3; Mpm1 = Mm4; Mpm4 = Mm7; Mpge4 = (M >= 9'd7);
            eq_rp = ({1'b0, rp} == Mm3); eq_lp = ({1'b0, lp} == Mm3); eq_a0 = ({1'b0, a0} == Mm3);
        end
        default: begin // A stored deletion removes 2, 3, or 4 old beads.
            Mp = Mm4; Mpm1 = Mm5; Mpm4 = Mm8; Mpge4 = (M >= 9'd8);
            eq_rp = ({1'b0, rp} == Mm4); eq_lp = ({1'b0, lp} == Mm4); eq_a0 = ({1'b0, a0} == Mm4);
        end
    endcase
end

// v = lp_n when the deletion does not start at 0 : lp / a0 / lm2 (= lp-lenL)
// wsl_n = v-3 (= wsl / wm1 / wm2) when v >= 3, else v + M' - 3 = M - (tot+3-v)
wire       v_ge3 = L0 ? lp_ge3 : (L1 ? a0_ge3 : lm2_ge3);
wire [7:0] v_m3  = L0 ? wsl    : (L1 ? wm1    : wm2);
wire [1:0] v_lo  = L0 ? lp[1:0] : (L1 ? a0[1:0] : lm2[1:0]);
wire [2:0] kd    = tot + 3'd3 - {1'b0, v_lo};
reg  [8:0] Msm;
always @(*) begin
    case (kd)
        3'd1:    Msm = Mm1;
        3'd2:    Msm = Mm2;
        3'd3:    Msm = Mm3;
        3'd4:    Msm = Mm4;
        3'd5:    Msm = Mm5;
        3'd6:    Msm = Mm6;
        default: Msm = Mm7;
    endcase
end

wire       eqend = L0 ? eq_rp : (L1 ? eq_lp : eq_a0);  // deletion reaches the end
wire [7:0] lp_n  = st_zero ? Mpm1[7:0] : (L0 ? lp : (L1 ? a0 : lm2));
wire [7:0] rp_n  = (st_zero | eqend) ? 8'd0 : st_c;
wire [7:0] wsl_n = st_zero ? (Mpge4 ? Mpm4[7:0] : Mpm1[7:0]) :
                   v_ge3   ? v_m3 : Msm[7:0];

//---------------------------------------------------------------------
//   Read-only walk (CNT)
//---------------------------------------------------------------------
wire [7:0] lp_w  = L1 ? a0  : lm2;
wire [7:0] wsl_w = L1 ? wm1 : wm2;
wire [7:0] rp_w  = (lenR == 2'd1) ? a3 : rp2;

//---------------------------------------------------------------------
//   Shot capture
//---------------------------------------------------------------------
wire [7:0] rp_s  = ({1'b0, shot_pos} == Mm1) ? 8'd0 : (shot_pos + 8'd1);
wire [8:0] sp_w  = {1'b0, shot_pos} + Mm3;
wire [7:0] wsl_s = (shot_pos >= 8'd3) ? (shot_pos - 8'd3) : sp_w[7:0];

//---------------------------------------------------------------------
//   Ring update
//---------------------------------------------------------------------
wire       md_ins  = ld_v | (is_l1 & ~elim);
wire       md_del  = ~ld_v & ((is_l1 & elim) | ((state == S_OUT) && (rem_out != 7'd0)));
wire       ins_emp = ld_v ? ld_first : emp;            // insert at index 0
wire [2:0] cin     = ld_v ? ld_c : c_r;                // otherwise insert at lp+1

wire [767:0] up1 = {cur[764:0], 3'd0};                 // up1[i] = ring[i-1]
wire [767:0] down1 = {3'd0, cur[767:3]};
wire [767:0] down2 = {6'd0, cur[767:6]};
wire [767:0] down3 = {9'd0, cur[767:9]};
wire [767:0] down4 = {12'd0, cur[767:12]};
wire shift1 = (sh == 3'd1);
wire shift2 = (sh == 3'd2);
wire shift3 = (sh == 3'd3);
wire shift4 = ~(shift1 | shift2 | shift3);

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
    wire take_del = md_del & ge_del;
    wire take_ins = ~md_del & md_ins & ge_ins;
    wire take_new = take_ins & eq_ins;
    wire take_up = take_ins & ~eq_ins;
    wire keep = ~(take_del | take_ins);
    assign nxt[3*g +: 3] =
        ({3{keep}} & cur[3*g +: 3]) |
        ({3{take_new}} & cin) |
        ({3{take_up}} & up1[3*g +: 3]) |
        ({3{take_del & shift1}} & down1[3*g +: 3]) |
        ({3{take_del & shift2}} & down2[3*g +: 3]) |
        ({3{take_del & shift3}} & down3[3*g +: 3]) |
        ({3{take_del & shift4}} & down4[3*g +: 3]);
end
endgenerate

always @(posedge clk) begin
    cur <= nxt;
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
        wsl        <= 8'd0;
        lp1        <= 8'd0;
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
                    wsl   <= wsl_s;
                end
            end
            S_EV1: begin
                if (elim) begin
                    M     <= Mp;
                    lp    <= lp_n;
                    rp    <= rp_n;
                    wsl   <= wsl_n;
                    if (elim2) begin
                        state <= S_CNT;
                        Mrem  <= Mp;
                        lp1   <= lp_n;
                        lv    <= 7'd1;
                        cnt1  <= tot + 3'd1;
                    end
                    else begin
                        state      <= S_OUT;
                        rem_out    <= 7'd0;
                        out_valid  <= 1'b1;
                        chain_num  <= 7'd1;
                        elim_color <= c_r;
                        elim_cnt   <= {6'd0, tot + 3'd1};
                    end
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
                if (elim2) begin
                    lv   <= lv + 7'd1;
                    Mrem <= Mr2;
                    lp   <= lp_w;
                    rp   <= rp_w;
                    wsl  <= wsl_w;
                end
                else begin
                    state      <= S_OUT;
                    rem_out    <= lv;
                    lp         <= lp1;
                    rp         <= rp1_restore;
                    wsl        <= wsl1_restore;
                    out_valid  <= 1'b1;
                    chain_num  <= lv + 7'd1;
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
                    wsl        <= wsl_n;
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

//############################################################################
//   4-entry window read : win[3j +: 3] = ring[st + j] (mod 256)
//   Entries are grouped in 4-entry blocks; blocks st>>2 and (st>>2)+1 are
//   one even and one odd block, read from two 32-block banks.
//############################################################################
module ZUMA_WIN (
    input      [767:0]  cur,
    input      [7:0]    st,
    output     [11:0]   win
);

genvar g;
wire [11:0] ev [0:31];
wire [11:0] od [0:31];
generate
for (g = 0; g < 32; g = g + 1) begin : G_BANK
    assign ev[g] = cur[24*g      +: 12];
    assign od[g] = cur[24*g + 12 +: 12];
end
endgenerate

wire [5:0]  b    = st[7:2];
wire [5:0]  bp1  = b + 6'd1;
wire [4:0]  eidx = b[0] ? bp1[5:1] : b[5:1];
wire [4:0]  oidx = b[5:1];
wire [11:0] E    = ev[eidx];
wire [11:0] O    = od[oidx];
wire [23:0] sq   = b[0] ? {E, O} : {O, E};             // block b, then b+1

reg  [11:0] w;
always @(*) begin
    case (st[1:0])
        2'd0:    w = sq[11:0];
        2'd1:    w = sq[14:3];
        2'd2:    w = sq[17:6];
        default: w = sq[20:9];
    endcase
end
assign win = w;

endmodule


