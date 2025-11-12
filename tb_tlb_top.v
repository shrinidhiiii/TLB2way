
`timescale 1ns / 1ps

module tlb_2way_full_tb;


  localparam integer NUM_SETS = 64;
  localparam integer K        = $clog2(NUM_SETS);
  localparam integer PA_WIDTH = 56;
  localparam integer VPN_BITS = 27;
  localparam integer PPN_BITS = (PA_WIDTH - 12);

  reg                   clk;
  reg                   rst_n;

  // Lookup 
  reg                   req_valid;
  reg  [63:0]           req_vaddr;
  reg  [15:0]           req_asid;
  reg                   req_is_store;

  wire                  resp_hit;
  wire [PPN_BITS-1:0]   resp_ppn;
  wire                  resp_R, resp_W, resp_X, resp_U, resp_G, resp_A, resp_D;

  // Refill 
  reg                   refill_valid;
  reg  [15:0]           refill_asid;
  reg  [VPN_BITS-1:0]   refill_vpn;
  reg  [PPN_BITS-1:0]   refill_ppn;
  reg                   refill_R, refill_W, refill_X, refill_U, refill_G, refill_A, refill_D;
  reg                   refill_vbit;

  // Maintenance 
  reg                   inv_all;
  reg                   inv_asid_valid;
  reg  [15:0]           inv_asid;
  reg                   inv_match_valid;
  reg  [15:0]           inv_match_asid;
  reg  [VPN_BITS-1:0]   inv_match_vpn;

  // Stats outputs (for debugging/verification)
  wire [31:0]           dbg_hits;
  wire [31:0]           dbg_misses;

  wire [1:0]            dbg_way_allocated;

  // refill set index
  wire [K-1:0] refill_set_idx;

  // providing test inputs
  bit[VPN_BITS-1:0] test_vpn;
  bit[15:0] test_asid;
 
  // instantiating the DUT 
   tlb_top #(
    .NUM_SETS (NUM_SETS),
    .PA_WIDTH (PA_WIDTH)
  ) DUT (
    // Clock/Reset
    .clk              (clk),
    .rst_n            (rst_n),
    // Lookup
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
    // Refill
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
    // Maintenance
    .inv_all          (inv_all),
    .inv_asid_valid   (inv_asid_valid),
    .inv_asid         (inv_asid),
    .inv_match_valid  (inv_match_valid),
    .inv_match_asid   (inv_match_asid),
    .inv_match_vpn    (inv_match_vpn),
    // Stats
    .dbg_hits         (dbg_hits),
    .dbg_misses       (dbg_misses),

    .dbg_way_allocated(dbg_way_allocated),
    .refill_set_idx   (refill_set_idx)

  );
  // to find set index
 
  initial begin
    clk =0;
    rst_n = 1;
    forever begin
      #5 clk = ~clk;
    end
  end

  task lookup;
    input [63:0] vaddr;
    input [15:0] asid;
    input is_store;
    input [PPN_BITS-1:0] exp_ppn; // not necessary

    begin
      req_vaddr = vaddr;
      req_asid = asid;
      req_is_store = is_store;
      req_valid = 1;
      @(negedge clk);  
      req_valid = 0;

      if (resp_hit != 1) begin
        $display("%t: ERROR Lookup MISMATCH:(ASID %h, VPN %h).", $time, asid, vaddr[38:12]);
      end else if (resp_hit && (resp_ppn != exp_ppn)) begin
        $display("%t: ERROR Lookup MISMATCH: PPN expected 0x%h, got 0x%h.",$time,
           exp_ppn, resp_ppn);
      end else if (resp_hit && is_store && resp_D == 0) begin
        $display("%t: ERROR: Hit on store, but D bit (0x%b) did not reflect the update.",$time, resp_D);
      end 
      else begin
        $display("lookup successful - HIT");
      end
    end
  endtask

  task refill;
    input [15:0] asid;
    input [VPN_BITS-1:0] vpn;
    input [PPN_BITS-1:0] ppn;
    input is_G;
    input is_A;
    input is_D;
    begin
      refill_asid = asid;
      refill_vpn = vpn;
      refill_ppn = ppn;
      refill_R = 1;
      refill_W = 1;
      refill_X = 1;
      refill_U = 1;
      refill_G = is_G;
      refill_A = is_A;
      refill_D = is_D;
      refill_vbit = 1;

      refill_valid = 1;
      @(negedge clk);

      if(dbg_way_allocated == 1) begin
        $display("%t: Refill (ASID %h, VPN %h) into set %d: Decision: Way 0",$time,asid,vpn,refill_set_idx);
      end 
      else if (dbg_way_allocated == 2)begin
        $display("%t: Refill (ASID %h, VPN %h)into set %d: Decision: Way 1", $time,asid,vpn,refill_set_idx);
      end 
      else begin
        $error("Refill error: Neither way was selected for allocation.");

      end 
      refill_valid = 0;

   end
  endtask

  task check_globalBit;
    input bit[15:0] asid;
    input bit[26:0] vpn;
    input bit exp_hit;
    input bit[PPN_BITS-1:0] ppn;
    input bit exp_G_bit;

    automatic bit[63:0] vaddr = {{25{1'b0}},vpn, {12{1'b0}}};

    req_vaddr = vaddr;
    req_asid = asid;
    req_valid = 1;

    @(negedge clk);
    req_valid =0;
    // checking hit & ppn
    if (resp_hit != exp_hit || (resp_hit && resp_ppn != ppn)) begin
        $error("FAIL: Hit/PPN mismatch.");
    end

     if (resp_hit) begin
        if (resp_G == exp_G_bit) begin
            $display("%t : PASS:(VPN %h) G-bit correctly set to %b.",$time, vpn, exp_G_bit);
        end else begin
            $error("%t: FAIL: G-bit mismatch. Expected %b, got %b.", $time,exp_G_bit, resp_G);
        end
    end 
  endtask 

  task check_dirtyBit;
    input bit[15:0] asid;
    input bit[26:0] vpn;
    input bit exp_hit;
    input bit[PPN_BITS-1:0] ppn;
    input bit exp_D_bit;

    automatic bit[63:0] vaddr = {{25{1'b0}},vpn, {12{1'b0}}};

    req_vaddr = vaddr;
    req_asid = asid;
    req_valid = 1;

    @(negedge clk);
    req_valid =0;
    // checking hit & ppn
    if (resp_hit != exp_hit || (resp_hit && resp_ppn != ppn)) begin
        $error("FAIL: Hit/PPN mismatch.");
    end

     if (resp_hit) begin
        if (resp_D == exp_D_bit) begin
            $display("%t: PASS:(VPN %h) D-bit correctly set to %b.", $time,vpn, exp_D_bit);
        end else begin
            $error("%t: FAIL: G-bit mismatch. Expected %b, got %b.", $time,exp_D_bit, resp_D);
        end
    end 
  endtask 

  task check_accessBit;
    input bit[15:0] asid;
    input bit[26:0] vpn;
    input bit exp_hit;
    input bit[PPN_BITS-1:0] ppn;
    input bit exp_A_bit;

    automatic bit[63:0] vaddr = {{25{1'b0}},vpn, {12{1'b0}}};

    req_vaddr = vaddr;
    req_asid = asid;
    req_valid = 1;

    @(negedge clk);
    req_valid =0;
    // checking hit & ppn
    if (resp_hit != exp_hit || (resp_hit && resp_ppn != ppn)) begin
        $error("FAIL: Hit/PPN mismatch.");
    end

     if (resp_hit) begin
        if (resp_A == exp_A_bit) begin
            $display("PASS:(VPN %h) A-bit correctly set to %b.", vpn, exp_A_bit);
        end else begin
            $error("FAIL: A-bit mismatch. Expected %b, got %b.", exp_A_bit, resp_A);
        end
    end 
  endtask 

  task invalidateAll;
    inv_all =1;
    @(negedge clk);
    inv_all =0;
    @(negedge clk);
    $display("%t: invalidate all",$time);
  endtask

  task invalidate_ASID;
    input bit[15:0] asid;

    inv_asid_valid = 1;
    inv_asid = asid;

    @(negedge clk);
    inv_asid_valid = 0;

    @(negedge clk);

     $display("%t: invalidated ASID: %h",$time,asid);
  endtask

  task invalidate_precise;
    input bit[15:0] asid;
    input bit[VPN_BITS-1:0] vpn;

    inv_match_asid = asid;
    inv_match_valid =1;
    inv_match_vpn = vpn;

    @(negedge clk);
    inv_match_valid =0;
    @(negedge clk);
    $display("%t: invalidated VPN: %h, ASID: %h", $time,vpn, asid);
  endtask

  task lookup_vs_invalidate;

    input bit[26:0] vpn;
    input bit[15:0] asid;

    automatic bit[63:0] vaddr = {{25{1'b0}},vpn, {12{1'b1}}};

    inv_match_asid = asid;
    inv_match_vpn = vpn;
    inv_match_valid = 1;

    req_vaddr = vaddr;
    req_asid = asid;
    req_valid = 1;

    @(negedge clk);
    inv_match_valid = 0;
    req_valid = 0;

    if(resp_hit == 0) begin
        $display("%t: lookup vs Invalidate PASS: Lookup resulted in MISS (Invalidate won).",$time);
    end else begin
        $error("%t: lookup vs Invalidate FAIL: Lookup resulted in HIT (Invalidate lost).",$time);
    end
  endtask

  task invalidate_vs_refill;


    input bit[15:0] asid;
    input bit[26:0] vpn;

    automatic bit[63:0] vaddr = {{25{1'b0}},vpn, {12{1'b1}}};

    inv_match_asid = asid;
    inv_match_vpn = vpn;
    inv_match_valid = 1;

    refill_vpn = vpn;
    refill_asid = asid;
    refill_valid = 1;
    refill_ppn = 'h1111;
    refill_R = 0;
    refill_W =0;
    refill_X =0;
    refill_U =0;
    refill_G =0;
    refill_A =0; 
    refill_D =0; 
    refill_vbit = 1; 

    @(negedge clk);
    inv_match_valid = 0;
    refill_valid = 0;

    $display("%t: expecting a miss - invalidation won", $time);
    lookup(vaddr, asid, 0, 'h1111);
  endtask 

  task lookup_vs_refill;

    input bit[15:0] asid;
    input bit[26:0] vpn;

    automatic bit[63:0] vaddr = {{25{1'b0}},vpn, {12{1'b1}}};

    req_vaddr = vaddr;
    req_asid = asid;
    req_valid = 1;

    refill_vpn = vpn;
    refill_asid = asid;
    refill_valid = 1;
    refill_ppn = 'h1111;
    refill_R = 0;
    refill_W =0;
    refill_X =0;
    refill_U =0;
    refill_G =0;
    refill_A =0; 
    refill_D =0; 
    refill_vbit = 1; 

    @(negedge clk);
    req_valid =0;
    refill_valid =0;

    $display("%t: lookup and refill to the same set, test should fail , lookup took priority", $time);
    lookup(vaddr, asid, 0, 'h1111);
  endtask 

  task hit_miss;
    input[26:0] vpn;
    input[15:0] asid;
    input is_store;
    input [PPN_BITS-1:0] exp_ppn;
    input is_G;
    input is_A;
    input is_D;

    automatic reg [63:0] vaddr = {{25{1'b0}},vpn, {12{1'b0}}};
    begin
        $display("%t: attempted lookup- expected to fail", $time);
        lookup(vaddr, asid, is_store, exp_ppn);
        refill(asid, vpn, exp_ppn, is_G, is_A, is_D);
        $display("%t:attempted lookup- expected hit", $time);
        lookup(vaddr, asid, is_store, exp_ppn);
        $display();

    end
  endtask 
    task basic_tests;

    $display("----------------basic hit and miss--------------");
        $display("expected set - 12");
        hit_miss(27'h123456, 16'h0001, 0, 'h1234, 0,0,0);
        $display();

        $display("expected set - 51");
        hit_miss(27'h3e5b1a0, 16'h1234, 0, 'h5678, 0,0,0);
        $display();

        $display("expected set - 17");
        hit_miss(27'h0, 16'h1111, 0, 'h2222, 0,0,0);
        $display();
        // same asid, different vpn
        $display("expected set - 22");
        hit_miss(27'h3e5b1a0, 16'h1111, 0, 'h5678, 0,0,0);
        $display();

        $display("expected set - 45");
        hit_miss(27'h123456, 16'h0020, 0, 'h1234, 0,0,0);
        $display();
        // same vpn, different asid 
        $display("expected set - 57");
        hit_miss(27'h123456, 16'h1234, 0, 'h5678, 0,0,0);
        $display();

        $display("-------------------------------------------------------");
    endtask

    task globalBit_test;
    $display("-----------------global entry bit----------");

        refill(16'h4444, 27'h123456, 'h1234, 1, 0, 0); // error
        check_globalBit(16'h4444,27'h123456, 1,'h1234,1);

        refill(16'h6784, 27'h123456, 'h5678, 1, 0, 0); // error
        check_globalBit(16'h6784,27'h123456, 1,'h1234,1);

        refill(16'hAAAA, 27'h876543, 'h9999, 1, 0, 0); // hit
        check_globalBit(16'hAAAA,27'h876543, 1, 'h9999, 1);

        $display("-------------------------------------------------------");
    endtask

    task dirtyBit_test;

    $display("-----------------dirty bit----------------------------");

        $display("setting dirty bit during refill");
        $display("dirty bit :1 - expected to pass");
        refill(16'h1234, 27'h654321, 'h4321, 1, 0, 1); 
        check_dirtyBit(16'h1234,27'h654321, 1,'h4321,1);

        $display("dirty bit :set to 0 ");
        refill(16'h4444, 27'h111111, 'h5555, 1, 0, 0); 
        check_dirtyBit(16'h4444, 27'h111111, 1,'h5555,0);

        $display("setting dirty bit during store instruction");
        refill(16'h2222, 27'h666666, 'h8888, 0, 0, 0); 
        lookup(64'h0000_0006_6666_6000, 16'h2222, 0, 'h8888);
        check_dirtyBit(16'h2222,27'h666666, 1,'h8888,0);

        $display("store ins:1 - expected to pass");
        refill(16'h7777, 27'h111111, 'h6666, 0, 0, 0); 
        lookup(64'h0000_0001_1111_1000, 16'h7777, 1, 'h6666);
        check_dirtyBit(16'h7777, 27'h111111, 1,'h6666,1);

        $display("-------------------------------------------------------");
    endtask

    task accessBit_test;

    $display("-----------------access bit---------------------------");

        $display("access bit set during refill");
        $display("expected to pass");
        refill(16'h9999, 27'h654321, 'h4321, 1, 1, 1); 
        check_accessBit(16'h9999,27'h654321, 1,'h4321,1);

        $display("during refill, access bit:0, expected to pass");
        refill(16'h9999, 27'h222222, 'h5555, 1, 0, 0); 
        check_accessBit(16'h9999, 27'h222222, 1,'h5555,1);

        lookup(64'h0000_0002_2222_2000,16'h9999,0,'h5555);
        $display("lookup for a non store, expected to pass");
        check_accessBit(16'h9999, 27'h222222, 1,'h5555,1);

        refill(16'h2222, 27'h0, 'h8888, 0, 0, 0); 
        lookup(64'h0, 16'h2222, 1, 'h8888);
        $display("lookup for a store, expected to pass");
        check_accessBit(16'h2222,27'h0, 1,'h8888,1);

        $display("-------------------------------------------------------");

    endtask

    task invalidateASID_test;

    $display("---------------invalidate by ASID -----------------------");

        // populating the arrays 
        // with ASID = 1111, RANDOM VPNs
        for(int i=0; i<20; i++) begin
            //automatic bit[26:0] rand_vpn = $urandom() & {27{1'b1}};
            automatic logic [26:0] rand_vpn = $urandom_range(0, (1<<27)-1);
            //automatic bit rand_g = $urandom_range(1,0);
            automatic logic rand_g = $urandom_range(0,1);
            refill(16'h1111, rand_vpn, 'h5578, rand_g, 0, 0);
        end 

        // with random ASID, same VPNs
        for(int i=0; i<20; i++) begin
            //automatic bit[15:0] ran = $urandom() & {16{1'b1}};
            automatic logic [15:0] ran = $urandom_range(0, 2**16-1);
            refill(ran, 27'b1, 'h1111, 0, 0, 0);
        end 

        refill(16'h1111, 27'h123456 , 'h5578, 1, 0, 0); // global entry

        invalidate_ASID(16'h1111);

        // check if its only invalidating entries with asid = 1111;
        $display("expected to pass - different ASID");
        lookup(64'h0000_0001_2345_6000, 16'h0020, 0, 'h1234); // expected to pass - set 45
        $display("expected to fail - invalidated ASID");
        lookup(64'b0, 16'h1111, 0, 'h2222); // expexcted to fail 

        // check if its not invalidating global entries with same ASID
        $display("expected to hit - global entry");
        lookup(64'h0000_0001_2345_6000, 16'h1111, 0,'h5578);
        

        $display("-------------------------------------------------------");

    endtask 

    task preciseInvalidate_test;

        $display("--------------- precise invalidate -----------------------");

        $display("expected to pass");
        lookup(64'h0000_0001_2345_6000, 16'h0020, 0, 'h1234); // expected to pass
        invalidate_precise(16'h0020, 27'h123456); // check set 45

        $display("expected to fail - precise invalidate");
        lookup(64'h0000_0001_2345_6000, 16'h0020, 0, 'h1234); // expected to fail

        // global entry 
        $display("precise invalidate for global entry");
        refill(16'h0007, 27'h0000007, 'h5578, 1, 0, 0);
        lookup(64'h0000_0000_0000_7000, 16'h0007, 0, 'h5578); // expected to pass
        
        invalidate_precise(16'h0007, 27'h0000007);
        lookup(64'h0000_0000_0000_7000, 16'h0007, 0, 'h5578);

        $display("-------------------------------------------------------");
    endtask

    task invalidateAll_test;

        $display("---------------invalidate all-----------------------");

        refill(16'h1234, 27'h123456, 'h5578, 0, 0, 0);
        $display("expected to pass");
        lookup(64'h0000_0001_2345_6000, 16'h1234, 0, 'h5578); 
        invalidateAll();
        $display("expected to fail - invalidate all");
        lookup(64'h0000_0001_2345_6000, 16'h1234, 0, 'h5578); 

        $display("-------------------------------------------------------");

    endtask

    task lru_test;

        $display("-----------------LRU testing--------------------");
        // 1. to check if its filling in way0 if both the ways are empty

        for(int i=0; i<64; i++) begin
        automatic bit[26:0]rand_vp;
        automatic bit[15:0]rand_asid;

        rand_vp = $urandom() & {27{1'b1}};
        rand_asid = $urandom() & {16{1'b1}};

        refill(rand_asid, rand_vp, 'h5578, 0,0,0);
        end  
/*
        $display("----------------LRU - display---------------------------");

        for(int i=0; i<NUM_SETS; i++) begin
            $display("set: %d, way0LRU: %h, way0valid: %d ||  way1LRU : %h way1valid: %d",i,DUT.w0_lru[i],DUT.w0_V[i] ,DUT.w1_lru[i], DUT.w1_V[i]);
        end 
        $display("-------------------------------------------------------");
*/
        //2. both the counters having same value - not possible unless both are 0, initial state
        refill(16'h0000, 27'h0000000, 'h5578, 0, 0, 0);
        refill(16'h0007, 27'h0000007, 'h5578, 0, 0, 0);


        // 3. checking the counters 
        $display("CHECKING LRU COUNTERS - set trashing(set0)");
        refill(16'h0000, 27'h0000000, 'h5578, 0, 0, 0);
        lookup(64'h0, 16'h0000, 0, 'h5578); 
        lookup(64'h0, 16'h0000, 0, 'h5578); 
        lookup(64'h0, 16'h0000, 0, 'h5578); 
        lookup(64'h0, 16'h0000, 0, 'h5578); 
        $display("LRU will be 5");
        refill(16'h0007, 27'h0000007, 'h5578, 0, 0, 0);
        $display("new refill happened in empty - way1");
        refill(16'h0000, 27'h001008, 'h5578, 0, 0, 0);
        $display("new refill happened in smaller LRU - way1");
        refill(16'h0008, 27'h0000008, 'h5578, 0, 0, 0);
        $display("new refill happened in smaller LRU - way1");
        $display("-------------------------------------------------------");

        // 4. checking for saturation 
        repeat(8) begin
        lookup(64'h0, 16'h0000, 0, 'h5578); 
        end
        // 5. checking for decrease in counter 
        lookup(64'h0000_0000_0000_8000, 16'h0008, 0, 'h5578);
        $display("way0 counter decreases and way1 counter increases. way0=6, way1=1");
        refill(16'h0000, 27'h001008, 'h5578, 0, 0, 0);
        $display("new refill happens at way1(victim), smaller LRU. way0 = 5, way1=2");

        // 6. both the counters having same value 
        inv_all = 1;
        @(negedge clk);
        inv_all = 0;
        @(negedge clk);

        refill(16'h0000, 27'h0000000, 'h5578, 0, 0, 0);
        refill(16'h0007, 27'h0000007, 'h5578, 0, 0, 0);
        $display("both the ways have lru = 1");
        lookup(64'h0, 16'h0000, 0, 'h5578); 

        /*
        $display("----------------LRU - display---------------------------");

        for(int i=0; i<NUM_SETS; i++) begin
            $display("set: %d, way0LRU: %h, way0valid: %d ||  way1LRU : %h way1valid: %d",i,DUT.w0_lru[i],DUT.w0_V[i] ,DUT.w1_lru[i], DUT.w1_V[i]);
        end 
        $display("-------------------------------------------------------");
    */
    endtask

    task raceCondition_test;


        $display("----------------race conditions ---------------------------");

        $display("----------------lookup vs invalidate - race----------------");
        $display("task: lookup_vs_invalidate : expecting a miss");
        lookup_vs_invalidate(27'h123456, 16'h1234);


        $display("----------------invalidate vs refill - race----------------");
        $display("task: invalidate_vs_refill : expecting a miss");
        invalidate_vs_refill(16'h1234, 27'h123456);

        $display("----------------lookup vs refill - race----------------");
        $display("task: lookup_vs_refill :  lookup will execute");

        refill(16'h0000, 27'h001008, 'h1111, 0,0,0);
        lookup_vs_refill(16'h0000, 27'h001008);
        $display("-------------------------------------------------------");
/*
        $display("----------------array values - display-------------------");
        for(int i=0; i<NUM_SETS; i++) begin
            $display("set: %d, way0VPN: %h, way0valid: %d, way0ASID : %h, way0G : %d,||  way1VPN : %h way1valid: %d, way1ASID : %h, way1G : %d",i,DUT.w0_VPN[i],DUT.w0_V[i],DUT.w0_ASID[i],DUT.w0_G[i] ,DUT.w1_VPN[i], DUT.w1_V[i], DUT.w1_ASID[i],DUT.w1_G[i]);
        end 
        $display("-------------------------------------------------------");
        */
    endtask

    
  initial begin
    
    // reset 
    rst_n =1;
    @(negedge clk);
    rst_n =0;
   @(negedge clk);
    rst_n =1;
    $display("initial reset complete");
    @(negedge clk);

    basic_tests();
    globalBit_test();
    dirtyBit_test();
    accessBit_test();
    invalidateASID_test();
    preciseInvalidate_test();
    invalidateAll_test();

    rst_n =0;
    @(negedge clk);
    @(negedge clk);
    rst_n =1;
    $display("reset complete");
    @(negedge clk);

    lru_test();
    raceCondition_test();
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

        $finish;
    end


endmodule