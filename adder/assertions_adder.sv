module binary_adder_4bit_assertions(input logic [3:0] A, 
                                    input logic [3:0] B, 
                                    input logic [3:0] SUM, 
                                    input logic COUT);

    // Formal property to check the addition correctness
    property addition_correctness;
        (SUM + (COUT << 4)) == (A + B);
    endproperty

    // Assert the property
    assert property (addition_correctness)
        else $fatal("Addition property failed: SUM + COUT does not equal A + B");
endmodule