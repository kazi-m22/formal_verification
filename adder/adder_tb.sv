module tb_binary_adder_4bit;


    logic [3:0] A;
    logic [3:0] B;
    logic [3:0] SUM;
    logic COUT;


    binary_adder_4bit dut (
        .A(A),
        .B(B),
        .SUM(SUM),
        .COUT(COUT)
    );





    initial begin
   
        A = 4'b0011; B = 4'b0101;
        #10;
        $display("A = %b, B = %b, expected sum = 1000, calculated sum = %b, expected cout = 0, calculated cout = %b", A, B, SUM, COUT);
	
        $stop;
    end
endmodule
