module LDPC (
    clk, rst_n, in_mode_valid, in_mode, in_data_valid, in_data,
    out_valid, out_data, out_warn
);
input clk, rst_n, in_mode_valid, in_mode, in_data_valid;
input signed [5:0] in_data;
output reg out_valid;
output wire signed [7:0] out_data;
output reg out_warn;

// Sixteen CNs process a complete layer per clock. In layer l, bank r
// contains column (r+l)%8, rotated into that layer's row alignment.
// Bank zero is absent; the 112 active edge reads are all fixed wires.
localparam [1:0] IDLE=2'd0, RECEIVE=2'd1, PROCESS=2'd2, OUTPUT_DATA=2'd3;
reg [1:0] state, layer;
reg mode;
reg [6:0] count;
reg [3:0] iteration;
reg signed [7:0] output_value;
reg [7:0] posterior [0:127];
reg [6:0] flood_base [0:127];

// Outgoing signs have even parity. Six signs determine the seventh.
// Four layers x 16 rows x {min1[4:0],min2[4:0],index[2:0],signs[5:0]}.
reg [1215:0] check_ring;
wire [303:0] new_checks;
wire [7:0] updated [0:127];
wire [4:0] magnitude_key [0:111];
wire [111:0] input_sign, new_sign;
wire [4:0] message_magnitude [0:111];
wire [63:0] syndrome_bits;
wire syndrome_clear=~(|syndrome_bits);
wire finish=(state==PROCESS && layer==2'd0 && iteration!=4'd0 &&
             (syndrome_clear || iteration==4'd8));
wire step_en=(state==PROCESS && !finish);
reg use_flood;              // registered: (!mode && layer!=0) of this cycle
reg old_par_r [0:15];       // parity of the 6 stored signs of the head slot

// Virtual shifts for absent columns make most layer transitions identical.
function integer alignment;
    input integer l, g;
    reg [31:0] shifts;
    begin
        case (l)
            0: shifts={4'd3,4'd9,4'd12,4'd13,4'd2,4'd10,4'd14,4'd0};
            1: shifts={4'd9,4'd12,4'd13,4'd2,4'd10,4'd14,4'd0,4'd5};
            2: shifts={4'd12,4'd13,4'd2,4'd10,4'd14,4'd0,4'd5,4'd0};
            default: shifts={4'd13,4'd2,4'd10,4'd14,4'd0,4'd5,4'd0,4'd7};
        endcase
        alignment=(shifts>>(g*4)) & 15;
    end
endfunction

// Constant source position for a destination bank/row in the NEXT layer.
// Evaluated at elaboration; no run-time barrel shifter is inferred.
function integer next_source;
    input integer l, r, q;
    integer n, g, s, k;
    begin
        n=(l+1)%4;
        g=(r+n)%8;
        s=(g-l+8)%8;
        k=(q+alignment(n,g)-alignment(l,g)+16)%16;
        next_source=s*16+k;
    end
endfunction




genvar slot, row, bank, lyr;
generate
    for (row=0;row<16;row=row+1) begin: ABSENT_BANK
        assign updated[row]=posterior[row];
    end

    for (slot=0;slot<7;slot=slot+1) begin: EDGE_SLOT
        for (row=0;row<16;row=row+1) begin: ROW
            localparam integer P=(slot+1)*16+row;
            localparam integer E=slot*16+row;
            wire [18:0] old_check=check_ring[row*19+:19];
            wire [4:0] old_mag=(old_check[8:6]==slot) ?
                              old_check[13:9] : old_check[18:14];
            wire old_negative;
            if (slot==6) begin: PARITY_SIGN
                assign old_negative=old_par_r[row];
            end else begin: STORED_SIGN
                assign old_negative=old_check[slot];
            end
            // Fuse signed magnitude conversion with the adder carry-in.
            // posterior-old_C2V is channel plus at most three other C2Vs:
            // [-100,100], so the eight-bit datapath is exact.
            wire [7:0] old_operand={8{~old_negative}} ^ {3'b000,old_mag};
            wire [7:0] without_old=posterior[P]+old_operand+{7'd0,~old_negative};
            wire [7:0] flood_without_old={flood_base[P][6],flood_base[P]}+
                                        old_operand+{7'd0,~old_negative};
            wire [7:0] v=use_flood ? flood_without_old : without_old;
            // |v| = ones_magnitude + v[7]. Normalizing here instead of after
            // the search is exact: round(0.75*m) is monotonic in m, so the
            // smallest normalized value is the normalized smallest value.
            // It keeps the search five bits wide and takes the scaling out
            // of the path between the search and the update adder.
            wire [6:0] ones_magnitude=v[6:0] ^ {7{v[7]}};
            wire saturated=(|ones_magnitude[6:5]) || (&ones_magnitude[4:0]);
            // Split m = 4*q + r + sign. Then round(3*m/4) is
            // 3*q + round(3*(r+sign)/4). The low correction is two bits,
            // so normalization needs one five-bit add, not two seven-bit adds.
            wire [2:0] q=ones_magnitude[4:2];
            wire [1:0] r=ones_magnitude[1:0];
            wire [4:0] triple_q={q[2]&q[1],
                                 q[2]^(q[1]&(q[2]|q[0])),
                                 q[2]^(q[1]&~q[0]),
                                 q[1]^q[0],q[0]};
            wire [1:0] correction={r[1]|(r[0]&v[7]),
                                    (~r[1]&(r[0]^v[7]))|(r[1]&r[0]&v[7])};
            wire [4:0] normalized=triple_q+{3'b000,correction};
            assign magnitude_key[E]=saturated ? 5'd23 : normalized;
            assign input_sign[E]=v[7];
            // Each group supplies its exclusion result directly. The global
            // second-minimum mux is used only by compressed-state storage.
            wire [4:0] new_mag=message_magnitude[E];
            wire [7:0] new_operand={8{new_sign[E]}} ^ {3'b000,new_mag};
            assign updated[P]=without_old+new_operand+{7'd0,new_sign[E]};
        end
    end

    // The four-input group uses two sorted pairs and parallel second-place
    // candidates. The three-input group keeps its shallow rank network.
    // Five + three local comparisons and three merge comparisons = eleven.
    for (row=0;row<16;row=row+1) begin: CHECK_UNIT
        wire [4:0] a0=magnitude_key[row];
        wire [4:0] a1=magnitude_key[16+row];
        wire [4:0] a2=magnitude_key[32+row];
        wire [4:0] a3=magnitude_key[48+row];
        wire [4:0] a4=magnitude_key[64+row];
        wire [4:0] a5=magnitude_key[80+row];
        wire [4:0] a6=magnitude_key[96+row];
        wire c01=a1<a0, c23=a3<a2;
        wire [4:0] p01=c01 ? a1 : a0;
        wire [4:0] q01=c01 ? a0 : a1;
        wire [4:0] p23=c23 ? a3 : a2;
        wire [4:0] q23=c23 ? a2 : a3;
        wire pick23=p23<p01;
        wire [4:0] lo_min1=pick23 ? p23 : p01;
        wire [4:0] lo_second01=(q01<p23) ? q01 : p23;
        wire [4:0] lo_second23=(q23<p01) ? q23 : p01;
        wire [4:0] lo_min2=pick23 ? lo_second23 : lo_second01;
        wire c45=a4<=a5, c46=a4<=a6, c56=a5<=a6;
        wire [2:0] hi_first={~c46 & ~c56, ~c45 & c56, c45 & c46};
        wire [2:0] hi_second={c46 ^ c56, c45 ^ ~c56, c45 ^ c46};
        wire [4:0] hi_min1=({5{hi_first[0]}} & a4)|
                            ({5{hi_first[1]}} & a5)|
                            ({5{hi_first[2]}} & a6);
        wire [4:0] hi_min2=({5{hi_second[0]}} & a4)|
                            ({5{hi_second[1]}} & a5)|
                            ({5{hi_second[2]}} & a6);
        wire [6:0] local_first;
        assign local_first[0]=~pick23 & ~c01;
        assign local_first[1]=~pick23 & c01;
        assign local_first[2]=pick23 & ~c23;
        assign local_first[3]=pick23 & c23;
        assign local_first[6:4]=hi_first;
        wire choose_hi=hi_min1<lo_min1;
        wire [4:0] min1=choose_hi ? hi_min1 : lo_min1;
        wire [4:0] second_if_lo=(lo_min2<hi_min1) ? lo_min2 : hi_min1;
        wire [4:0] second_if_hi=(hi_min2<lo_min1) ? hi_min2 : lo_min1;
        wire [4:0] min2=choose_hi ? second_if_hi : second_if_lo;
        wire [6:0] is_min1;
        wire [6:0] signs;
        wire sign_parity=input_sign[row]^input_sign[16+row]^input_sign[32+row]^
                         input_sign[48+row]^input_sign[64+row]^
                         input_sign[80+row]^input_sign[96+row];
        for (slot=0;slot<7;slot=slot+1) begin: MESSAGE_OUT
            if (slot<4) begin: GROUP_FOUR
                assign is_min1[slot]=local_first[slot] & ~choose_hi;
                // If this group's winner is not the global winner, this
                // candidate equals min1, so no global-winner gating is needed.
                assign message_magnitude[slot*16+row]=local_first[slot] ?
                    second_if_lo : min1;
            end else begin: GROUP_THREE
                assign is_min1[slot]=local_first[slot] & choose_hi;
                assign message_magnitude[slot*16+row]=local_first[slot] ?
                    second_if_hi : min1;
            end
            assign signs[slot]=sign_parity^input_sign[slot*16+row];
            assign new_sign[slot*16+row]=signs[slot];
        end
        wire [2:0] min_index={is_min1[4]|is_min1[5]|is_min1[6],
                              is_min1[2]|is_min1[3]|is_min1[6],
                              is_min1[1]|is_min1[3]|is_min1[5]};
        assign new_checks[row*19+:19]={min1,min2,min_index,signs[5:0]};
    end

    for (bank=0;bank<8;bank=bank+1) begin: STORAGE_BANK
        for (row=0;row<16;row=row+1) begin: ROW
            localparam integer P=bank*16+row;
            localparam integer S0=next_source(0,bank,row);
            localparam integer S1=next_source(1,bank,row);
            localparam integer S2=next_source(2,bank,row);
            localparam integer S3=next_source(3,bank,row);
            localparam integer VN=bank*16+(row+alignment(0,bank))%16;
            localparam integer NG=((VN+1)%128)/16;
            localparam integer NQ=((VN+1)%16-alignment(0,NG)+16)%16;
            wire [7:0] serial_next;
            if (VN==127) begin: TAIL
                assign serial_next={{2{in_data[5]}},in_data};
            end else begin: CHAIN
                assign serial_next=posterior[NG*16+NQ];
            end
            reg [7:0] rotated_next;
            always @(*) begin
                case (layer)
                    2'd0: rotated_next=updated[S0];
                    2'd1: rotated_next=updated[S1];
                    2'd2: rotated_next=updated[S2];
                    default: rotated_next=updated[S3];
                endcase
            end
            // No hold state: when not decoding, the array simply shifts.
            // Extra shifts before the input burst are overwritten by the
            // 128 input shifts, so no enable/hold mux is needed.
            always @(posedge clk) begin
                posterior[P]<=step_en ? rotated_next : serial_next;
            end

            // Layer zero reads the previous posterior directly and captures
            // the flooding snapshot for layer one. Later layers only rotate it.
            wire [7:0] snap=posterior[S0];
            wire [6:0] clipped_snap=(snap[7]==snap[6]) ? snap[6:0] :
                                    {snap[7],{6{~snap[7]}}};
            // Clipping to [-64,63] preserves the subsequent V2C clip after
            // subtracting any C2V in [-23,23].
            always @(posedge clk) begin
                case (layer)
                    2'd0: flood_base[P]<=clipped_snap;
                    2'd1: flood_base[P]<=flood_base[S1];
                    default: flood_base[P]<=flood_base[S2];
                endcase
            end
        end
    end

    // Syndrome is observed only at an iteration boundary, in layer-0 layout.
    for (lyr=0;lyr<4;lyr=lyr+1) begin: SYNDROME_LAYER
        for (row=0;row<16;row=row+1) begin: ROW
            wire [7:0] bits_in;
            for (bank=0;bank<8;bank=bank+1) begin: COLUMN
                localparam integer Q=(row+alignment(lyr,bank)-alignment(0,bank)+16)%16;
                if (bank==lyr) begin: ABSENT
                    assign bits_in[bank]=1'b0;
                end else begin: PRESENT
                    assign bits_in[bank]=posterior[bank*16+Q][7];
                end
            end
            assign syndrome_bits[lyr*16+row]=^bits_in;
        end
    end
endgenerate

// Receive flushes the ring before decoding. No reset or hold mux is needed
// on the 1216 stored message bits.
wire in_process=(state==PROCESS);
always @(posedge clk) begin
    check_ring<={new_checks & {304{in_process}},check_ring[1215:304]};
end

// The ring shifts every clock, so the next head is slot 1 now. Pre-compute
// the parity of its six stored signs (the seventh C2V sign) one cycle early.
genvar prow;
generate
    for (prow=0;prow<16;prow=prow+1) begin: PARITY_PRE
        always @(posedge clk) old_par_r[prow]<=^check_ring[304+prow*19 +: 6];
    end
endgenerate

// output_value is already zero whenever out_valid is low
assign out_data=output_value;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state<=IDLE;
        layer<=2'd0;
        iteration<=4'd0;
        mode<=1'b0;
        count<=7'd0;
        output_value<=8'sd0;
        out_valid<=1'b0;
        out_warn<=1'b0;
        use_flood<=1'b0;
    end else begin
        // next-cycle value of (!mode && layer!=0); only used in PROCESS
        use_flood<=(state==PROCESS) && !mode && (layer!=2'd3);
        case (state)
            IDLE: begin
                if (in_mode_valid) begin
                    mode<=in_mode;
                    count<=7'd0;
                    layer<=2'd0;
                    iteration<=4'd0;
                    state<=RECEIVE;
                end
            end
            RECEIVE: begin
                if (in_data_valid) begin
                    if (count==7'd127) begin
                        count<=7'd0;
                        state<=PROCESS;
                    end else count<=count+7'd1;
                end
            end
            PROCESS: begin
                // Check the completed iteration while the next layer-zero
                // datapath evaluates; suppress its write when decoding ends.
                if (finish) begin
                    output_value<=posterior[0];
                    out_valid<=1'b1;
                    out_warn<=!syndrome_clear;
                    count<=7'd0;
                    state<=OUTPUT_DATA;
                end else begin
                    layer<=layer+2'd1;
                    if (layer==2'd3) iteration<=iteration+4'd1;
                end
            end
            OUTPUT_DATA: begin
                if (count==7'd127) begin
                    output_value<=8'sd0;
                    out_valid<=1'b0;
                    out_warn<=1'b0;
                    state<=IDLE;
                end else begin
                    output_value<=posterior[0];
                    count<=count+7'd1;
                end
            end
            default: state<=IDLE;
        endcase
    end
end
endmodule
