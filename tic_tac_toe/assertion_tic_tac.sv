
module tic_tac_toe_formal;

    // Game grid: initially all cells are empty
    logic [1:0] board [8:0]; // 2-bit per cell: 10 for empty, 01 for A, 00 for B

    // Inputs
    logic clk;                  // Clock
    logic reset;                // Reset
    logic [3:0] move_A, move_B; // Moves by Player A and B (0 to 8 positions)
    logic turn;                 // 1: Player A's turn, 0: Player B's turn

    // Task to simulate a player's move
    task make_move(input logic [3:0] pos, input logic player);
        if (board[pos] == 2'b10) begin
            board[pos] = (player) ? 2'b01 : 2'b00; // Mark position for A or B
        end
    endtask

    // Property: Player A can always avoid losing
    property no_loss_possible_A;
        // Assumption: Game starts with an empty grid and it's Player A's turn
        @(posedge clk)
        (reset && turn == 1) |-> ##1
        always
            // There must exist a move for Player A that prevents a loss
            (|({board[0] == 2'b10, board[1] == 2'b10, board[2] == 2'b10, 
                board[3] == 2'b10, board[4] == 2'b10, board[5] == 2'b10, 
                board[6] == 2'b10, board[7] == 2'b10, board[8] == 2'b10}) &&
            !check_win(2'b00)); // Player B cannot win on the next move
    endproperty

    // Check-win function (logic as per the original module)
    function logic check_win(input logic [1:0] player);
        check_win = 0;
        // Check rows
        if ((board[0] == player && board[1] == player && board[2] == player) ||
            (board[3] == player && board[4] == player && board[5] == player) ||
            (board[6] == player && board[7] == player && board[8] == player))
            check_win = 1;
        // Check columns
        else if ((board[0] == player && board[3] == player && board[6] == player) ||
                 (board[1] == player && board[4] == player && board[7] == player) ||
                 (board[2] == player && board[5] == player && board[8] == player))
            check_win = 1;
        // Check diagonals
        else if ((board[0] == player && board[4] == player && board[8] == player) ||
                 (board[2] == player && board[4] == player && board[6] == player))
            check_win = 1;
    endfunction

    // Property binding
    assert_no_loss_possible_A : assert property (no_loss_possible_A);

endmodule
