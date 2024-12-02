
module binary_adder_4bit (
    input  logic [3:0] A,  
    input  logic [3:0] B, 
    output logic [3:0] SUM, 
    output logic COUT      
);
    logic [3:0] carry;     
    logic [3:0] xor_ab;    
    logic [3:0] and_ab;  
    logic [3:0] sum_intermediate; 

 
    assign xor_ab[0] = ~(~A[0] & ~B[0]) & ~(A[0] & B[0]); 
    assign and_ab[0] = A[0] & B[0]; 
    assign sum_intermediate[0] = ~(~xor_ab[0] & ~1'b0) & ~(xor_ab[0] & 1'b0); 
    assign carry[0] = and_ab[0]; 


    assign xor_ab[1] = ~(~A[1] & ~B[1]) & ~(A[1] & B[1]);
    assign and_ab[1] = A[1] & B[1]; 
    assign sum_intermediate[1] = ~(~xor_ab[1] & ~carry[0]) & ~(xor_ab[1] & carry[0]); 
    assign carry[1] = and_ab[1] | (carry[0] & xor_ab[1]);

  
    assign xor_ab[2] = ~(~A[2] & ~B[2]) & ~(A[2] & B[2]); 
    assign and_ab[2] = A[2] & B[2];
    assign sum_intermediate[2] = ~(~xor_ab[2] & ~carry[1]) & ~(xor_ab[2] & carry[1]); 
    assign carry[2] = and_ab[2] | (carry[1] & xor_ab[2]); 


    assign xor_ab[3] = ~(~A[3] & ~B[3]) & ~(A[3] & B[3]); 
    assign and_ab[3] = A[3] & B[3]; 
    assign sum_intermediate[3] = ~(~xor_ab[3] & ~carry[2]) & ~(xor_ab[3] & carry[2]); 
    assign carry[3] = and_ab[3] | (carry[2] & xor_ab[3]);


    assign SUM = sum_intermediate; 
    assign COUT = carry[3];

endmodule