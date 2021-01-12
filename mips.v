`timescale 1ns/1ps
`define mydelay 1

//--------------------------------------------------------------
// mips.v
// David_Harris@hmc.edu and Sarah_Harris@hmc.edu 23 October 2005
// Single-cycle MIPS processor
//--------------------------------------------------------------

// single-cycle MIPS processor
module mips(input         clk, reset,
            output [31:0] pc,
            input  [31:0] instr,
            output        memwrite,
            output [31:0] memaddr,
            output [31:0] memwritedata,
            input  [31:0] memreaddata);

// ###### Yongwoo kim: Start #######

  wire pcmove;
  wire pc_en, if_id_en, id_ex_en, ex_mem_en, mem_wb_en;
  wire if_id_reset, id_ex_reset, ex_mem_reset, mem_wb_reset;

  wire id_forward_a, id_forward_b;
  wire [1:0] ex_forward_a, ex_forward_b;

  wire [31:0] if_pcplus4, id_pcplus4, ex_pcplus4;
  wire [31:0] instr_reset, id_instr, ex_instr;

  wire [2:0] id_if_control, ex_if_control;
  wire [2:0] id_if_control_reset;
  wire [1:0] id_wb_control, ex_wb_control, mem_wb_control, wb_wb_control;
  wire [1:0] id_wb_control_reset, ex_wb_control_reset, mem_wb_control_reset;
  wire [0:0] id_mem_control, ex_mem_control, mem_mem_control;
  wire [0:0] id_mem_control_reset, ex_mem_control_reset;
  wire [8:0] id_ex_control, ex_ex_control;
  wire [8:0] id_ex_control_reset;
  wire [31:0] id_rd1, ex_rd1;
  wire [31:0] id_rd2, ex_rd2, ex_rd2_forward, mem_rd2;

  wire ex_pcsrc;
  wire [31:0] ex_pcbranch, ex_pcjump, ex_pcjr;
  wire [31:0] ex_aluout, mem_aluout, wb_aluout;
  wire [4:0] ex_dst, mem_dst, wb_dst;

  wire [31:0] wb_memreaddata;
  wire [31:0] wb_writedata;

  assign #`mydelay pcmove = ex_pcsrc | ex_if_control[1] | ex_if_control[0];

  hazard_detection hd(
    .id_rs        (id_instr[25:21]),
    .id_rt        (id_instr[20:16]),
    .ex_rt        (ex_instr[20:16]),
    .ex_memtoreg  (ex_wb_control[1]),
    .pcmove       (pcmove),

    .if_id_reset  (if_id_reset),
    .id_ex_reset  (id_ex_reset),
    .ex_mem_reset (ex_mem_reset),
    .mem_wb_reset (mem_wb_reset),
    .pc_en        (pc_en),
    .if_id_en     (if_id_en),
    .id_ex_en     (id_ex_en),
    .ex_mem_en    (ex_mem_en),
    .mem_wb_en    (mem_wb_en));

  forwarding_unit fu(
    .id_rs          (id_instr[25:21]),
    .id_rt          (id_instr[20:16]),
    .ex_rs          (ex_instr[25:21]),
    .ex_rt          (ex_instr[20:16]),
    .mem_dst        (mem_dst),
    .wb_dst         (wb_dst),
    .mem_regwrite   (mem_wb_control[0]),
    .wb_regwrite    (wb_wb_control[0]),
    .ex_forward_a   (ex_forward_a),
    .ex_forward_b   (ex_forward_b),
    .id_forward_a   (id_forward_a),
    .id_forward_b   (id_forward_b));

// ===========if============

  instruction_fetch inst_f(
    .clk      (clk),
    .reset    (reset),
    .en       (pc_en),
    .pcbranch (ex_pcbranch),
    .pcjump   (ex_pcjump),
    .pcjr     (ex_pcjr),
    .pcsrc    (ex_pcsrc),
    .jump     (ex_if_control[1]),
    .jr       (ex_if_control[0]),
    .pc       (pc),
    .pcplus4  (if_pcplus4));

// ===========ff============

  flopenr #(32) if_id_pcplus4(
    .clk  (clk),
    .reset(reset),
    .en   (if_id_en),
    .d    (if_pcplus4),
    .q    (id_pcplus4));

  assign #`mydelay instr_reset = if_id_reset ? 32'b0 : instr;

  flopenr #(32) if_id_instr(
    .clk  (clk),
    .reset(reset),
    .en   (if_id_en),
    .d    (instr_reset),
    .q    (id_instr));

// ===========id============

  instruction_decode id(
    .clk          (clk),
    .reset        (reset),
    .RegWrite     (wb_wb_control[0]),
    .instr        (id_instr),
    .writereg     (wb_dst),
    .writedata    (wb_writedata),
    .forward_a    (id_forward_a),
    .forward_b    (id_forward_b),
                          
    .if_control   (id_if_control),
    .wb_control   (id_wb_control),
    .mem_control  (id_mem_control),
    .ex_control   (id_ex_control),
    .rd1          (id_rd1),
    .rd2          (id_rd2));

// ===========ff============

  assign #`mydelay id_if_control_reset = id_ex_reset ? 3'b0 : id_if_control;

  flopenr #(3) id_ex_if_control(
    .clk  (clk),
    .reset(reset),
    .en   (id_ex_en),
    .d    (id_if_control_reset),
    .q    (ex_if_control));

  assign #`mydelay id_wb_control_reset = id_ex_reset ? 2'b0 : id_wb_control;

  flopenr #(2) id_ex_wb_control(
    .clk  (clk),
    .reset(reset),
    .en   (id_ex_en),
    .d    (id_wb_control_reset),
    .q    (ex_wb_control));

  assign #`mydelay id_mem_control_reset = id_ex_reset ? 1'b0 : id_mem_control;

  flopenr #(1) id_ex_mem_control(
    .clk  (clk),
    .reset(reset),
    .en   (id_ex_en),
    .d    (id_mem_control_reset),
    .q    (ex_mem_control));

  assign #`mydelay id_ex_control_reset = id_ex_reset ? 9'b0 : id_ex_control;

  flopenr #(9) id_ex_ex_control(
    .clk  (clk),
    .reset(reset),
    .en   (id_ex_en),
    .d    (id_ex_control_reset),
    .q    (ex_ex_control));

  flopenr #(32) id_ex_rd1(
    .clk  (clk),
    .reset(reset),
    .en   (id_ex_en),
    .d    (id_rd1),
    .q    (ex_rd1));

  flopenr #(32) id_ex_rd2(
    .clk  (clk),
    .reset(reset),
    .en   (id_ex_en),
    .d    (id_rd2),
    .q    (ex_rd2));

  flopenr #(32) id_ex_pcplus4(
    .clk  (clk),
    .reset(reset),
    .en   (id_ex_en),
    .d    (id_pcplus4),
    .q    (ex_pcplus4));

  flopenr #(32) id_ex_instr(
    .clk  (clk),
    .reset(reset),
    .en   (id_ex_en),
    .d    (id_instr),
    .q    (ex_instr));

// ===========ex============

  execution ex(
  .instr        (ex_instr),
  .pcplus4      (ex_pcplus4),
  .branch       (ex_if_control[2]),
  .signext      (ex_ex_control[8]),
  .shiftl16     (ex_ex_control[7]),
  .alusrc       (ex_ex_control[6]),
  .regdst       (ex_ex_control[5]),
  .link         (ex_ex_control[4]),
  .alusign      (ex_ex_control[3]),
  .alucontrol   (ex_ex_control[2:0]),
  .rd1          (ex_rd1),
  .rd2          (ex_rd2),
  .forward_a    (ex_forward_a),
  .forward_b    (ex_forward_b),
  .mem_aluout   (mem_aluout),
  .wb_aluout    (wb_writedata),

  .pcsrc        (ex_pcsrc),
  .pcbranch     (ex_pcbranch),
  .pcjump       (ex_pcjump),
  .pcjr         (ex_pcjr),
  .ex_aluout    (ex_aluout),
  .rd2_forward  (ex_rd2_forward),
  .dst          (ex_dst));
   
// ===========ff============

  assign #`mydelay ex_wb_control_reset = ex_mem_reset ? 2'b0 : ex_wb_control;

  flopenr #(2) ex_mem_wb_control(
    .clk  (clk),
    .reset(reset),
    .en   (ex_mem_en),
    .d    (ex_wb_control_reset),
    .q    (mem_wb_control));

  assign #`mydelay ex_mem_control_reset = ex_mem_reset ? 1'b0 : ex_mem_control;

  flopenr #(1) ex_mem_mem_control(
    .clk  (clk),
    .reset(reset),
    .en   (ex_mem_en),
    .d    (ex_mem_control_reset),
    .q    (mem_mem_control));

  flopenr #(32) ex_mem_aluout(
    .clk  (clk),
    .reset(reset),
    .en   (ex_mem_en),
    .d    (ex_aluout),
    .q    (mem_aluout));

  flopenr #(32) ex_mem_rd2(
    .clk  (clk),
    .reset(reset),
    .en   (ex_mem_en),
    .d    (ex_rd2_forward),
    .q    (mem_rd2));

  flopenr #(5) ex_mem_dst(
    .clk  (clk),
    .reset(reset),
    .en   (ex_mem_en),
    .d    (ex_dst),
    .q    (mem_dst));

// ===========mem============

  assign memaddr = mem_aluout;
  assign memwritedata = mem_rd2;
  assign memwrite = mem_mem_control[0];

// ===========ff============

  assign #`mydelay mem_wb_control_reset = mem_wb_reset ? 2'b0 : mem_wb_control;

  flopenr #(2) mem_wb_wb_control(
    .clk  (clk),
    .reset(reset),
    .en   (mem_wb_en),
    .d    (mem_wb_control_reset),
    .q    (wb_wb_control));

  flopenr #(32) mem_wb_memreaddata(
    .clk  (clk),
    .reset(reset),
    .en   (mem_wb_en),
    .d    (memreaddata),
    .q    (wb_memreaddata));

  flopenr #(32) mem_wb_aluout(
    .clk  (clk),
    .reset(reset),
    .en   (mem_wb_en),
    .d    (mem_aluout),
    .q    (wb_aluout));

  flopenr #(5) mem_wb_dst(
    .clk  (clk),
    .reset(reset),
    .en   (mem_wb_en),
    .d    (mem_dst),
    .q    (wb_dst));

// ===========wb============

  mux2 #(32) writedatamux(
    .d0 (wb_aluout),
    .d1 (wb_memreaddata),
    .s  (wb_wb_control[1]),
    .y  (wb_writedata));

endmodule

module hazard_detection (input [4:0] id_rs,
                         input [4:0] id_rt,
                         input [4:0] ex_rt,
                         input ex_memtoreg,
                         input pcmove,
                         output if_id_reset, id_ex_reset, ex_mem_reset, mem_wb_reset,
                         output pc_en, if_id_en, id_ex_en, ex_mem_en, mem_wb_en);

  reg [8:0] controls;
                 
  assign {if_id_reset, id_ex_reset, ex_mem_reset, mem_wb_reset,
          pc_en, if_id_en, id_ex_en, ex_mem_en, mem_wb_en} = controls;

  always @(*)
    if (ex_memtoreg && (ex_rt == id_rs || ex_rt == id_rt))
      begin
        if (pcmove) controls <= #`mydelay 9'b110000111;
        else controls <= #`mydelay 9'b010000111;
      end
    else 
      begin
        if (pcmove) controls <= #`mydelay 9'b110011111;
        else controls <= #`mydelay 9'b000011111;
      end
  
endmodule

module instruction_fetch(input clk, reset, en,
                         input [31:0] pcbranch,
                         input [31:0] pcjump,
                         input [31:0] pcjr,
                         input pcsrc, jump, jr,

                         output [31:0] pc,
                         output [31:0] pcplus4);

  wire [31:0] pcnextbr, pcnextjump, pcnext;

  adder pcadd1(
    .a (pc),
    .b (32'b100),
    .y (pcplus4));

  mux2 #(32) pcbrmux(
    .d0  (pcplus4),
    .d1  (pcbranch),
    .s   (pcsrc),
    .y   (pcnextbr));

  mux2 #(32) pcjumpmux(
    .d0   (pcnextbr),
    .d1   (pcjump),
    .s    (jump),
    .y    (pcnextjump));

  mux2 #(32) pcjrmux(
    .d0   (pcnextjump),
    .d1   (pcjr),
    .s    (jr),
    .y    (pcnext));

  flopenr #(32) pcreg(
    .clk   (clk),
    .reset (reset),
    .en    (en),
    .d     (pcnext),
    .q     (pc));

endmodule

module instruction_decode(input clk, reset,
                          input RegWrite,
                          input [31:0] instr,
                          input [4:0] writereg,
                          input [31:0] writedata,

                          input forward_a,
                          input forward_b,
                          
                          output [2:0] if_control,
                          output [1:0] wb_control,
                          output [0:0] mem_control,
                          output [8:0] ex_control,

                          output [31:0] rd1,
                          output [31:0] rd2);

  wire zero, alusign;
  wire signext, shiftl16, memtoreg, memwrite, branch, alusrc;
  wire regdst, regwrite, jump, link, jr;
  wire [2:0] alucontrol;
  wire [31:0] ext_imm, signimmsh, rtrd, dst, sum;
  wire [31:0] rd1_not_forward, rd2_not_forward;

  controller c(
    .op         (instr[31:26]), 
    .funct      (instr[5:0]), 
    .signext    (signext),
    .shiftl16   (shiftl16),
    .memtoreg   (memtoreg),
    .memwrite   (memwrite),
    .branch     (branch),
    .alusrc     (alusrc),
    .regdst     (regdst),
    .regwrite   (regwrite),
    .jump       (jump),
    .link       (link),
    .jr         (jr),
    .alucontrol (alucontrol));

  assign alusign = alusrc ? ~signext : instr[0];

  assign if_control = {branch, jump, jr};
  assign wb_control = {memtoreg, regwrite};
  assign mem_control = {memwrite};
  assign ex_control = {signext, shiftl16, alusrc, regdst, link, alusign, alucontrol};
  
  regfile rf(
    .clk     (clk),
    .we      (RegWrite),
    .ra1     (instr[25:21]),
    .ra2     (instr[20:16]),
    .wa      (writereg),
    .wd      (writedata),
    .rd1     (rd1_not_forward),
    .rd2     (rd2_not_forward));

  mux2 #(32) rd1mux(
    .d0 (rd1_not_forward),
    .d1 (writedata),
    .s  (forward_a),
    .y  (rd1));

  mux2 #(32) rd2mux(
    .d0 (rd2_not_forward),
    .d1 (writedata),
    .s  (forward_b),
    .y  (rd2));

endmodule

module execution(input [31:0] instr,
                 input [31:0] pcplus4,
                 input branch,
                 input signext, shiftl16, alusrc, regdst, link,
                 input alusign,
                 input [2:0] alucontrol,
                 input [31:0] rd1,
                 input [31:0] rd2,
                 input [1:0] forward_a,
                 input [1:0] forward_b,
                 input [31:0] mem_aluout,
                 input [31:0] wb_aluout,
                 output pcsrc,
                 output [31:0] pcbranch, pcjump, pcjr,
                 output [31:0] ex_aluout,
                 output reg [31:0] rd2_forward,
                 output [4:0] dst);

  reg [31:0] srca; 
  wire [31:0] srcb;
  wire [31:0] ext_imm, shiftedimm, signimmsh;
  wire [4:0] rtrd;
  wire [31:0] aluout;
  wire zero;

  always @(*)
  begin
    case(forward_a)
    2'b01 : srca <= #`mydelay mem_aluout;
    2'b10 : srca <= #`mydelay wb_aluout;
    default : srca <= #`mydelay rd1;
   endcase
  end

  always @(*)
  begin
    case(forward_b)
    2'b01 : rd2_forward <= #`mydelay mem_aluout;
    2'b10 : rd2_forward <= #`mydelay wb_aluout;
    default : rd2_forward <= #`mydelay rd2;
   endcase
  end

  sign_zero_ext sze(
    .a       (instr[15:0]),
    .signext (signext),
    .y       (ext_imm));

  shift_left_16 sl16(
    .a         (ext_imm),
    .shiftl16  (shiftl16),
    .y         (shiftedimm));

  mux2 #(32) srcbmux(
    .d0 (rd2_forward),
    .d1 (shiftedimm),
    .s  (alusrc),
    .y  (srcb));

  alu alu(
    .a       (srca),
    .b       (srcb),
    .alucont (alucontrol),
    .alusign (alusign),
    .result  (aluout),
    .zero    (zero));

  sl2 immsh(
    .a (ext_imm),
    .y (signimmsh));

  adder pcadd2(
    .a (pcplus4),
    .b (signimmsh),
    .y (pcbranch));

  mux2 #(5) rtrdmux(
    .d0 (instr[20:16]),
    .d1 (instr[15:11]),
    .s  (regdst),
    .y  (rtrd));

  mux2 #(5) dstlinkmux(
    .d0 (rtrd),
    .d1 (5'b11111),
    .s  (link),
    .y  (dst));

  mux2 #(32) datalinkmux(
    .d0 (aluout),
    .d1 (pcplus4),
    .s  (link),
    .y  (ex_aluout));

  assign #`mydelay pcsrc = instr[26] ? (branch & ~zero) : (branch & zero);
  assign #`mydelay pcjump = {pcplus4[31:28],instr[25:0],2'b00};
  assign #`mydelay pcjr = srca;

endmodule

module forwarding_unit(input [4:0] id_rs,
                       input [4:0] id_rt,
                       input [4:0] ex_rs,
                       input [4:0] ex_rt,
                       input [4:0] mem_dst,
                       input [4:0] wb_dst,
                       input mem_regwrite,
                       input wb_regwrite,
                       output reg [1:0] ex_forward_a,
                       output reg [1:0] ex_forward_b,
                       output reg id_forward_a,
                       output reg id_forward_b);
                
  always @(*)
  begin
      if((ex_rs == mem_dst) && mem_regwrite) ex_forward_a <= #`mydelay 2'b01;
      else if((ex_rs == wb_dst) && wb_regwrite) ex_forward_a <= #`mydelay 2'b10;
      else ex_forward_a <= #`mydelay 2'b00;
  end

  always @(*)
  begin
    if((ex_rt == mem_dst) && mem_regwrite) ex_forward_b <= #`mydelay 2'b01;
    else if((ex_rt == wb_dst) && wb_regwrite) ex_forward_b <= #`mydelay 2'b10;
    else ex_forward_b <= #`mydelay 2'b00;
  end

  always @(*)
  begin
    if((id_rs == wb_dst) && wb_regwrite) id_forward_a <= #`mydelay 1'b1;
    else id_forward_a <= #`mydelay 1'b0;
  end

  always @(*)
  begin
    if((id_rt == wb_dst) && wb_regwrite) id_forward_b <= #`mydelay 1'b1;
    else id_forward_b <= #`mydelay 1'b0;
  end

endmodule

module controller(input  [5:0] op, funct,
                  output       signext,
                  output       shiftl16,
                  output       memtoreg, memwrite,
                  output       branch, alusrc,
                  output       regdst, regwrite,
                  output       jump, link, jr,
                  output [2:0] alucontrol);

  wire [2:0] aluop;

  maindec md(
    .op       (op),
    .signext  (signext),
    .shiftl16 (shiftl16),
    .memtoreg (memtoreg),
    .memwrite (memwrite),
    .branch   (branch),
    .alusrc   (alusrc),
    .regdst   (regdst),
    .regwrite (regwrite),
    .jump     (jump),
    .link     (link),
    .aluop    (aluop));

  aludec ad( 
    .funct      (funct),
    .aluop      (aluop), 
    .alucontrol (alucontrol),
    .jr         (jr));

endmodule

module maindec(input  [5:0] op,
               output       signext,
               output       shiftl16,
               output       memtoreg, memwrite,
               output       branch, alusrc,
               output       regdst, regwrite,
               output       jump, link,
               output [2:0] aluop);

  reg [12:0] controls;

  assign {signext, shiftl16, regwrite, regdst, alusrc, branch, memwrite,
          memtoreg, jump, link, aluop} = controls;

  always @(*)
    case(op)
      6'b000000: controls <= #`mydelay 13'b0011000000111; // Rtype
      6'b100011: controls <= #`mydelay 13'b1010100100000; // LW
      6'b101011: controls <= #`mydelay 13'b1000101000000; // SW
      6'b000100: controls <= #`mydelay 13'b1000010000001; // BEQ
      6'b000101: controls <= #`mydelay 13'b1000010000001; // BNE
      6'b001000, 
      6'b001001: controls <= #`mydelay 13'b1010100000000; // ADDI, ADDIU: only difference is exception
      6'b001010: controls <= #`mydelay 13'b1010100000011; // SLTI
      6'b001101: controls <= #`mydelay 13'b0010100000010; // ORI
      6'b001111: controls <= #`mydelay 13'b0110100000000; // LUI
      6'b000010: controls <= #`mydelay 13'b0000000010000; // J
      6'b000011: controls <= #`mydelay 13'b0010000011000; // JAL
      default:   controls <= #`mydelay 13'bxxxxxxxxxxxxx; // ???
    endcase

endmodule

module aludec(input      [5:0] funct,
              input      [2:0] aluop,
              output reg [2:0] alucontrol,
              output jr);

  assign #`mydelay jr = ((aluop == 3'b111) && (funct == 6'b001000)); // JR

  always @(*)
    case(aluop)
      3'b000: alucontrol <= #`mydelay 3'b010;  // add
      3'b001: alucontrol <= #`mydelay 3'b110;  // sub
      3'b010: alucontrol <= #`mydelay 3'b001;  // or
      3'b011: alucontrol <= #`mydelay 3'b111;  // slt
      default: case(funct)          // RTYPE
          6'b000000: alucontrol <= #`mydelay 3'b000; // nop. 0 and 0
          6'b100000,
          6'b100001: alucontrol <= #`mydelay 3'b010; // ADD, ADDU: only difference is exception
          6'b100010,
          6'b100011: alucontrol <= #`mydelay 3'b110; // SUB, SUBU: only difference is exception
          6'b100100: alucontrol <= #`mydelay 3'b000; // AND
          6'b100101: alucontrol <= #`mydelay 3'b001; // OR
          6'b101010,
          6'b101011: alucontrol <= #`mydelay 3'b111; // SLT, SLTU: control it at ALU
          default:   alucontrol <= #`mydelay 3'bxxx; // ???
        endcase
    endcase

endmodule

// ###### Yongwoo kim: End ####### 