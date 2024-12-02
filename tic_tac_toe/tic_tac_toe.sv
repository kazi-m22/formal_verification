
module tic_tac_toe (
    input logic clk,                // Clock signal
    input logic reset,              // Reset signal to restart the game
    input logic [3:0] position,     // Position input for the current player's move (0 to 8 for the 3x3 grid)
    input logic player_select,      // Player selection: 1 for Player A, 0 for Player B
    output logic current_turn,      // 1 if Player A's turn, 0 if Player B's turn
    output logic [1:0] game_status  // 00: Draw, 01: A wins, 10: B wins, 11: Game in progress
);

    // Parameters
    parameter EMPTY = 2'b10;

    // Game board (3x3 grid flattened to 1D)
    logic [1:0] board [8:0];

    // State variables
    logic [3:0] moves;              // Count of moves made
    logic game_over;                // Indicates if the game has ended

    // Initialize the board and game state
    task initialize_game;
        integer i;
        begin
            for (i = 0; i < 9; i = i + 1) begin
                board[i] = EMPTY;   // Mark all cells as empty
            end
            current_turn = 1;       // Player A starts
            game_status = 2'b11;    // Game in progress
            moves = 0;              // No moves made yet
            game_over = 0;          // Game is not over
        end
    endtask

    // Function to check for a win
    function logic check_win(input logic [1:0] player);
        begin
            check_win = 0;

            // Rows
            if ((board[0] == player && board[1] == player && board[2] == player) ||
                (board[3] == player && board[4] == player && board[5] == player) ||
                (board[6] == player && board[7] == player && board[8] == player)) begin
                check_win = 1;
            end
            // Columns
            else if ((board[0] == player && board[3] == player && board[6] == player) ||
                     (board[1] == player && board[4] == player && board[7] == player) ||
                     (board[2] == player && board[5] == player && board[8] == player)) begin
                check_win = 1;
            end
            // Diagonals
            else if ((board[0] == player && board[4] == player && board[8] == player) ||
                     (board[2] == player && board[4] == player && board[6] == player)) begin
                check_win = 1;
            end
        end
    endfunction

    // Game logic
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            initialize_game();
        end else if (!game_over) begin
            // Check if the move is valid
            if (board[position] == EMPTY && player_select == current_turn) begin
                // Update the board
                board[position] = (current_turn) ? 2'b01 : 2'b00; // 1 for Player A, 0 for Player B
                moves = moves + 1;

                // Check for a win
                if (check_win(board[position])) begin
                    game_status = (current_turn) ? 2'b01 : 2'b10; // 01: A wins, 10: B wins
                    game_over = 1;
                end
                // Check for a draw
                else if (moves == 9) begin
                    game_status = 2'b00; // Draw
                    game_over = 1;
                end
                // Switch turns
                else begin
                    current_turn = ~current_turn;
                end
            end
        end
    end
endmodule
