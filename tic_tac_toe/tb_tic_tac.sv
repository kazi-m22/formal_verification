
`timescale 1ns / 1ps

module tic_tac_toe_tb;

    // Inputs
    logic clk;
    logic reset;
    logic [3:0] position;
    logic player_select;

    // Outputs
    logic current_turn;
    logic [1:0] game_status;

    // Instantiate the Tic-Tac-Toe module
    tic_tac_toe uut (
        .clk(clk),
        .reset(reset),
        .position(position),
        .player_select(player_select),
        .current_turn(current_turn),
        .game_status(game_status)
    );

    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;

    // Task to make a move
    task make_move(input logic [3:0] pos, input logic player);
        begin
            position = pos;
            player_select = player;
            @(posedge clk); // Wait for a clock edge
        end
    endtask

    // Test sequence
    initial begin
        // Initialize inputs
        reset = 0;
        position = 0;
        player_select = 0;

        // Reset the game
        $display("Starting the Tic-Tac-Toe Testbench...");
        reset = 1;
        @(posedge clk); // Wait for a clock edge
        reset = 0;

        // Simulate moves
        // Player A (1) moves first
        $display("Player A places 1 at position 0.");
        make_move(4'd0, 1);

        // Player B (0) moves next
        $display("Player B places 0 at position 1.");
        make_move(4'd1, 0);

        // Player A (1) moves again
        $display("Player A places 1 at position 3.");
        make_move(4'd3, 1);

        // Player B (0) moves
        $display("Player B places 0 at position 4.");
        make_move(4'd4, 0);

        // Player A (1) moves to complete a row
        $display("Player A places 1 at position 6.");
        make_move(4'd6, 1);

        // Observe results
        if (game_status == 2'b01) begin
            $display("Player A wins!");
        end else if (game_status == 2'b10) begin
            $display("Player B wins!");
        end else if (game_status == 2'b00) begin
            $display("Game ends in a draw.");
        end else begin
            $display("Game is still in progress.");
        end

        // Reset the game and test for a draw
        $display("Resetting the game for a draw scenario...");
        reset = 1;
        @(posedge clk);
        reset = 0;

        // Fill the board without any winner
        make_move(4'd0, 1);
        make_move(4'd1, 0);
        make_move(4'd2, 1);
        make_move(4'd3, 0);
        make_move(4'd4, 1);
        make_move(4'd5, 0);
        make_move(4'd6, 1);
        make_move(4'd7, 0);
        make_move(4'd8, 1);

        // Observe results
        if (game_status == 2'b01) begin
            $display("Player A wins!");
        end else if (game_status == 2'b10) begin
            $display("Player B wins!");
        end else if (game_status == 2'b00) begin
            $display("Game ends in a draw.");
        end else begin
            $display("Game is still in progress.");
        end

        $display("Testbench completed.");
        $finish;
    end
endmodule