`ifndef TLB_TOP_V
`define TLB_TOP_V

`timescale 1ns/1ps

module tlb_top #(
  parameter integer NUM_SETS  = 64,
  parameter integer PA_WIDTH  = 56,
  parameter integer VPN_BITS  = 27,
  parameter integer PPN_BITS  = (PA_WIDTH - 12)
)(
  input  wire                   clk,
  input  wire                   rst_n,

  // Lookup
  input  wire                   req_valid,
  input  wire [63:0]            req_vaddr,
  input  wire [15:0]            req_asid,
  input  wire                   req_is_store,

  output wire                   resp_hit,
  output wire [PPN_BITS-1:0]    resp_ppn,
  output wire                   resp_R,
  output wire                   resp_W,
  output wire                   resp_X,
  output wire                   resp_U,
  output wire                   resp_G,
  output wire                   resp_A,
  output wire                   resp_D,

  // Refill interface
  input  wire                   refill_valid,
  input  wire [15:0]            refill_asid,
  input  wire [VPN_BITS-1:0]    refill_vpn,
  input  wire [PPN_BITS-1:0]    refill_ppn,
  input  wire                   refill_R,
  input  wire                   refill_W,
  input  wire                   refill_X,
  input  wire                   refill_U,
  input  wire                   refill_G,
  input  wire                   refill_A,
  input  wire                   refill_D,
  input  wire                   refill_vbit,

  // Invalidate control
  input  wire                   inv_all,
  input  wire                   inv_asid_valid,
  input  wire [15:0]            inv_asid,
  input  wire                   inv_match_valid,
  input  wire [15:0]            inv_match_asid,
  input  wire [VPN_BITS-1:0]    inv_match_vpn,

  // Debug/statistics
  output wire [31:0]            dbg_hits,
  output wire [31:0]            dbg_misses,

  output wire [5:0]             refill_set_idx,
  output wire [1:0]             dbg_way_allocated

);

  // -----------------------------
  // DUT instantiation
  // -----------------------------
  tlb_2way #(
    .NUM_SETS (NUM_SETS),
    .PA_WIDTH (PA_WIDTH),
    .VPN_BITS (VPN_BITS),
    .PPN_BITS (PPN_BITS)
  ) dut (
    .clk              (clk),
    .rst_n            (rst_n),

    .req_valid        (req_valid),
    .req_vaddr        (req_vaddr),
    .req_asid         (req_asid),
    .req_is_store     (req_is_store),

    .resp_hit         (resp_hit),
    .resp_ppn         (resp_ppn),
    .resp_R           (resp_R),
    .resp_W           (resp_W),
    .resp_X           (resp_X),
    .resp_U           (resp_U),
    .resp_G           (resp_G),
    .resp_A           (resp_A),
    .resp_D           (resp_D),

    .refill_valid     (refill_valid),
    .refill_asid      (refill_asid),
    .refill_vpn       (refill_vpn),
    .refill_ppn       (refill_ppn),
    .refill_R         (refill_R),
    .refill_W         (refill_W),
    .refill_X         (refill_X),
    .refill_U         (refill_U),
    .refill_G         (refill_G),
    .refill_A         (refill_A),
    .refill_D         (refill_D),
    .refill_vbit      (refill_vbit),

    .inv_all          (inv_all),
    .inv_asid_valid   (inv_asid_valid),
    .inv_asid         (inv_asid),
    .inv_match_valid  (inv_match_valid),
    .inv_match_asid   (inv_match_asid),
    .inv_match_vpn    (inv_match_vpn),

    .dbg_hits         (dbg_hits),
    .dbg_misses       (dbg_misses),

    .dbg_way_allocated(dbg_way_allocated),
    .refill_set_idx   (refill_set_idx)
  
  );

endmodule

`endif


`ifndef TLB_HASH_V
`define TLB_HASH_V

module tlb_hash #(
  parameter integer K = 6  // log2(NUM_SETS)
)(
  input  wire [15:0] asid,
  input  wire [26:0] vpn,   // {vpn2[26:18], vpn1[17:9], vpn0[8:0]}
  output wire [K-1:0] idx
);
  wire [8:0] vpn0 = vpn[8:0];
  wire [8:0] vpn1 = vpn[17:9];
  wire [8:0] vpn2 = vpn[26:18];

  // Fold ASID to K bits (if K<=16 just take low K)
  wire [K-1:0] asid_fold;
  generate
    if (K <= 16) begin : G_ASID_LOW
      assign asid_fold = asid[K-1:0];
    end 
    else begin : G_ASID_FOLD
      // Generic XOR-fold for K>16 (rare)
      reg [K-1:0] tmp;
      integer i;
      always @* begin
        tmp = {K{1'b0}};
        for (i=0; i<16; i=i+1) begin
          tmp[i%K] = tmp[i%K] ^ asid[i];
        end
      end
      assign asid_fold = tmp;
    end
  endgenerate

  // Build a K-bit mix from 9-bit fields:
  // replicate/xor-fold to K bits safely
  function [K-1:0] fold9;
    input [8:0] x;
    integer j;
    begin
      fold9 = {K{1'b0}};
      for (j=0; j<9; j=j+1) begin
        fold9[j%K] = fold9[j%K] ^ x[j];
      end
    end
  endfunction

  wire [K-1:0] f0 = fold9(vpn0);
  wire [K-1:0] f1 = fold9(vpn1);
  wire [K-1:0] f2 = fold9(vpn2);

  assign idx = f0 ^ f1 ^ f2 ^ asid_fold;

endmodule

`endif

// tlb_2way.v
// Verilog-2001, compatible with Verilator v38.
// Sv39 2-way set-associative TLB (no megapages), 3-bit LRU, way0-first fill.
// Tags: (ASID, VPN). G=1 bypasses ASID on match. TLB.V is occupancy (cache state).

`ifndef TLB_2WAY_V
`define TLB_2WAY_V

module tlb_2way #(
  parameter integer NUM_SETS = 64,     // power of two
  parameter integer PA_WIDTH = 56,     // typical Sv39
  parameter integer VPN_BITS = 27,     // 39-12
  parameter integer PPN_BITS = (PA_WIDTH - 12)
)(
  input  wire                   clk,
  input  wire                   rst_n,

  // Lookup
  input  wire                   req_valid,
  input  wire [63:0]            req_vaddr,     // canonical Sv39 VA
  input  wire [15:0]            req_asid,
  input  wire                   req_is_store,  // 1=store/AMO, 0=load/fetch

  output reg                    resp_hit,
  output reg  [PPN_BITS-1:0]    resp_ppn,
  output reg                    resp_R,
  output reg                    resp_W,
  output reg                    resp_X,
  output reg                    resp_U,
  output reg                    resp_G,
  output reg                    resp_A,
  output reg                    resp_D,

  // Refill/allocate from PTW
  input  wire                   refill_valid,
  input  wire [15:0]            refill_asid,
  input  wire [VPN_BITS-1:0]    refill_vpn,    // {vpn2,vpn1,vpn0}
  input  wire [PPN_BITS-1:0]    refill_ppn,
  input  wire                   refill_R,
  input  wire                   refill_W,
  input  wire                   refill_X,
  input  wire                   refill_U,
  input  wire                   refill_G,
  input  wire                   refill_A,
  input  wire                   refill_D,
  input  wire                   refill_vbit,   // occupancy for TLB slot

  // Maintenance (kept minimal)
  input  wire                   inv_all,       // flush all
  input  wire                   inv_asid_valid,
  input  wire [15:0]            inv_asid,      // flush non-G entries of this ASID
  input  wire                   inv_match_valid,
  input  wire [15:0]            inv_match_asid,// precise inv by (ASID,VPN) or any ASID if global
  input  wire [VPN_BITS-1:0]    inv_match_vpn,

  // Stats (optional)
  output reg  [31:0]            dbg_hits,
  output reg  [31:0]            dbg_misses,

  output reg  [1:0]             dbg_way_allocated,
  output reg  [5:0]           refill_set_idx

);
  localparam integer K = clog2(NUM_SETS);
  //reg [1:0]                 dbg_way_allocated; // 1 if Way 0 was selected for refill, 2 if way1 was selected 
  // -------------------------
  // Helper: integer clog2()
  // -------------------------
  function integer clog2;
    input integer value;
    integer v;
    begin
      v = value - 1;
      clog2 = 0;
      while (v > 0) begin
        v = v >> 1;
        clog2 = clog2 + 1;
      end
    end
  endfunction

  // -------------------------
  // Extract VPN from VA
  // -------------------------
  wire [8:0]  req_vpn2 = req_vaddr[38:30];
  wire [8:0]  req_vpn1 = req_vaddr[29:21];
  wire [8:0]  req_vpn0 = req_vaddr[20:12];
  wire [VPN_BITS-1:0] req_vpn = {req_vpn2, req_vpn1, req_vpn0};

  // -------------------------
  // Hash index (modular)
  // -------------------------
  wire [K-1:0] idx_req, idx_refill, idx_inv;
  tlb_hash #(.K(K)) u_hash_req (
    .asid (req_asid),
    .vpn  (req_vpn),
    .idx  (idx_req)
  );
  tlb_hash #(.K(K)) u_hash_refill (
    .asid (refill_asid),
    .vpn  (refill_vpn),
    .idx  (idx_refill)
  );
  tlb_hash #(.K(K)) u_hash_inv (
    .asid (inv_match_asid),
    .vpn  (inv_match_vpn),
    .idx  (idx_inv)
  );

 
     


  // --------------------------------------
  // State arrays: two ways, split per field
  // --------------------------------------

  // Way 0 arrays
  reg                  w0_V      [0:NUM_SETS-1];
  reg [15:0]           w0_ASID   [0:NUM_SETS-1];
  reg [VPN_BITS-1:0]   w0_VPN    [0:NUM_SETS-1];
  reg [PPN_BITS-1:0]   w0_PPN    [0:NUM_SETS-1];
  reg                  w0_D      [0:NUM_SETS-1];
  reg                  w0_A      [0:NUM_SETS-1];
  reg                  w0_G      [0:NUM_SETS-1];
  reg                  w0_U      [0:NUM_SETS-1];
  reg                  w0_X      [0:NUM_SETS-1];
  reg                  w0_W      [0:NUM_SETS-1];
  reg                  w0_R      [0:NUM_SETS-1];
  reg [2:0]            w0_lru    [0:NUM_SETS-1];

  // Way 1 arrays
  reg                  w1_V      [0:NUM_SETS-1];
  reg [15:0]           w1_ASID   [0:NUM_SETS-1];
  reg [VPN_BITS-1:0]   w1_VPN    [0:NUM_SETS-1];
  reg [PPN_BITS-1:0]   w1_PPN    [0:NUM_SETS-1];
  reg                  w1_D      [0:NUM_SETS-1];
  reg                  w1_A      [0:NUM_SETS-1];
  reg                  w1_G      [0:NUM_SETS-1];
  reg                  w1_U      [0:NUM_SETS-1];
  reg                  w1_X      [0:NUM_SETS-1];
  reg                  w1_W      [0:NUM_SETS-1];
  reg                  w1_R      [0:NUM_SETS-1];
  reg [2:0]            w1_lru    [0:NUM_SETS-1];

  // -------------------------
  // Combinational compare
  // -------------------------
  reg hit0, hit1;
  reg use_way0;

  // Match helpers
  function automatic is_match;
    input               V;
    input               G;
    input [15:0]        ASID;
    input [VPN_BITS-1:0]VPN;
    input [15:0]        asid_q;
    input [VPN_BITS-1:0]vpn_q;
    begin
      if (!V) is_match = 1'b0;
      else if (G) is_match = (VPN == vpn_q);
      else        is_match = (ASID == asid_q) && (VPN == vpn_q);
    end
  endfunction

  always @* begin
    // defaults
    resp_hit = 1'b0;
    resp_ppn = {PPN_BITS{1'b0}};
    resp_R   = 1'b0;
    resp_W   = 1'b0;
    resp_X   = 1'b0;
    resp_U   = 1'b0;
    resp_G   = 1'b0;
    resp_A   = 1'b0;
    resp_D   = 1'b0;

    hit0 = is_match(w0_V[idx_req], w0_G[idx_req], w0_ASID[idx_req], w0_VPN[idx_req], req_asid, req_vpn);
    hit1 = is_match(w1_V[idx_req], w1_G[idx_req], w1_ASID[idx_req], w1_VPN[idx_req], req_asid, req_vpn);

    resp_hit = hit0 | hit1;

    // prefer way0 on both (should not happen often)
    use_way0 = (hit0) ? 1'b1 :
               (hit1) ? 1'b0 :
                        1'b1;


    if (hit0) begin
      resp_ppn = w0_PPN[idx_req];
      resp_R   = w0_R[idx_req];
      resp_W   = w0_W[idx_req];
      resp_X   = w0_X[idx_req];
      resp_U   = w0_U[idx_req];
      resp_G   = w0_G[idx_req];
      resp_A   = w0_A[idx_req];
      resp_D   = w0_D[idx_req];
    end else if (hit1) begin
      resp_ppn = w1_PPN[idx_req];
      resp_R   = w1_R[idx_req];
      resp_W   = w1_W[idx_req];
      resp_X   = w1_X[idx_req];
      resp_U   = w1_U[idx_req];
      resp_G   = w1_G[idx_req];
      resp_A   = w1_A[idx_req];
      resp_D   = w1_D[idx_req];
    end

    refill_set_idx = u_hash_refill.idx;
  end

  // 3-bit saturating helpers
  function [2:0] sat_inc3;
    input [2:0] x;
    begin
      if (x == 3'b111) sat_inc3 = 3'b111;
      else             sat_inc3 = x + 3'd1;
    end
  endfunction
  function [2:0] sat_dec3;
    input [2:0] x;
    begin
      if (x == 3'b000) sat_dec3 = 3'b000;
      else             sat_dec3 = x - 3'd1;
    end
  endfunction

  // Victim select: least counter; tie -> way0
  function pick_victim_way;
    input [2:0] c0, c1;
    begin
      if (c0 == c1) pick_victim_way = 1'b0;
      else          pick_victim_way = (c0 < c1) ? 1'b0 : 1'b1;
    end
  endfunction

  integer i;

  // Stats
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      dbg_hits   <= 32'd0;
      dbg_misses <= 32'd0;
    end else if (req_valid) begin
      if (resp_hit) dbg_hits   <= dbg_hits + 32'd1;
      else          dbg_misses <= dbg_misses + 32'd1;
    end
  end

  // Main seq: reset, invalidate, A/D update, refill
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (i=0; i<NUM_SETS; i=i+1) begin
        w0_V[i]   <= 1'b0; w1_V[i]   <= 1'b0;
        w0_ASID[i]<= 16'd0; w1_ASID[i]<=16'd0;
        w0_VPN[i] <= {VPN_BITS{1'b0}}; w1_VPN[i] <= {VPN_BITS{1'b0}};
        w0_PPN[i] <= {PPN_BITS{1'b0}}; w1_PPN[i] <= {PPN_BITS{1'b0}};
        w0_D[i]   <= 1'b0; w1_D[i]   <= 1'b0;
        w0_A[i]   <= 1'b0; w1_A[i]   <= 1'b0;
        w0_G[i]   <= 1'b0; w1_G[i]   <= 1'b0;
        w0_U[i]   <= 1'b0; w1_U[i]   <= 1'b0;
        w0_X[i]   <= 1'b0; w1_X[i]   <= 1'b0;
        w0_W[i]   <= 1'b0; w1_W[i]   <= 1'b0;
        w0_R[i]   <= 1'b0; w1_R[i]   <= 1'b0;
        w0_lru[i] <= 3'd0; w1_lru[i] <= 3'd0;
      end
    end else begin
      // Invalidate ops (priority before updates/refills)
      if (inv_all) begin
        for (i=0; i<NUM_SETS; i=i+1) begin
          w0_V[i] <= 1'b0; w1_V[i] <= 1'b0;
        end
      end else begin
        if (inv_asid_valid) begin
          for (i=0; i<NUM_SETS; i=i+1) begin
            if (w0_V[i] && !w0_G[i] && (w0_ASID[i] == inv_asid)) w0_V[i] <= 1'b0;
            if (w1_V[i] && !w1_G[i] && (w1_ASID[i] == inv_asid)) w1_V[i] <= 1'b0;
          end
        end
        if (inv_match_valid) begin
          // precise invalidate: match VPN and (ASID or G)
          for (i=0; i<NUM_SETS; i=i+1) begin
            if (w0_V[i] && (w0_VPN[i] == inv_match_vpn) &&
               (w0_G[i] || (w0_ASID[i] == inv_match_asid))) w0_V[i] <= 1'b0;
            if (w1_V[i] && (w1_VPN[i] == inv_match_vpn) &&
               (w1_G[i] || (w1_ASID[i] == inv_match_asid))) w1_V[i] <= 1'b0;
          end
        end
      end

      // On lookup hit: update A/D and LRU
      if (req_valid && resp_hit) begin
        if (hit0) begin
          w0_A[idx_req]   <= 1'b1;
          if (req_is_store) w0_D[idx_req] <= 1'b1;
          w0_lru[idx_req] <= sat_inc3(w0_lru[idx_req]);
          w1_lru[idx_req] <= sat_dec3(w1_lru[idx_req]);
        end else if (hit1) begin
          w1_A[idx_req]   <= 1'b1;
          if (req_is_store) w1_D[idx_req] <= 1'b1;
          w1_lru[idx_req] <= sat_inc3(w1_lru[idx_req]);
          w0_lru[idx_req] <= sat_dec3(w0_lru[idx_req]);
        end
      end

      // Refill/allocate
      if (refill_valid) begin
        bit[5:0] s;
        s = idx_refill;

        if (!w0_V[s]) begin
          // Fill way0 first if free
          dbg_way_allocated <= 1;
          w0_V[s]    <= refill_vbit;
          w0_ASID[s] <= refill_asid;
          w0_VPN[s]  <= refill_vpn;
          w0_PPN[s]  <= refill_ppn;
          w0_R[s]    <= refill_R;
          w0_W[s]    <= refill_W;
          w0_X[s]    <= refill_X;
          w0_U[s]    <= refill_U;
          w0_G[s]    <= refill_G;
          w0_A[s]    <= refill_A;
          w0_D[s]    <= refill_D;

          w0_lru[s]  <= sat_inc3(w0_lru[s]);
          w1_lru[s]  <= sat_dec3(w1_lru[s]);

        end else if (!w1_V[s]) begin
          // Fill way1 if way0 occupied but way1 free
          dbg_way_allocated <= 2;
          w1_V[s]    <= refill_vbit;
          w1_ASID[s] <= refill_asid;
          w1_VPN[s]  <= refill_vpn;
          w1_PPN[s]  <= refill_ppn;
          w1_R[s]    <= refill_R;
          w1_W[s]    <= refill_W;
          w1_X[s]    <= refill_X;
          w1_U[s]    <= refill_U;
          w1_G[s]    <= refill_G;
          w1_A[s]    <= refill_A;
          w1_D[s]    <= refill_D;

          w1_lru[s]  <= sat_inc3(w1_lru[s]);
          w0_lru[s]  <= sat_dec3(w0_lru[s]);

        end else begin
          // Both full: replace least counter; tie -> way0
          if (pick_victim_way(w0_lru[s], w1_lru[s]) == 1'b0) begin
            dbg_way_allocated <= 1;
            w0_V[s]    <= refill_vbit;
            w0_ASID[s] <= refill_asid;
            w0_VPN[s]  <= refill_vpn;
            w0_PPN[s]  <= refill_ppn;
            w0_R[s]    <= refill_R;
            w0_W[s]    <= refill_W;
            w0_X[s]    <= refill_X;
            w0_U[s]    <= refill_U;
            w0_G[s]    <= refill_G;
            w0_A[s]    <= refill_A;
            w0_D[s]    <= refill_D;

            w0_lru[s]  <= sat_inc3(w0_lru[s]);
            w1_lru[s]  <= sat_dec3(w1_lru[s]);
          end else begin
            dbg_way_allocated <= 2;
            w1_V[s]    <= refill_vbit;
            w1_ASID[s] <= refill_asid;
            w1_VPN[s]  <= refill_vpn;
            w1_PPN[s]  <= refill_ppn;
            w1_R[s]    <= refill_R;
            w1_W[s]    <= refill_W;
            w1_X[s]    <= refill_X;
            w1_U[s]    <= refill_U;
            w1_G[s]    <= refill_G;
            w1_A[s]    <= refill_A;
            w1_D[s]    <= refill_D;

            w1_lru[s]  <= sat_inc3(w1_lru[s]);
            w0_lru[s]  <= sat_dec3(w0_lru[s]);
          end
        end
      end
    end
  end

 

endmodule

`endif

