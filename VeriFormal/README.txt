
This folder contains all Isabelle/HOL theories (VeriFormal), encoding examples, and
the OCaml code of VeriFormal. 

******** Executing Verilog designs in VeriFormal *********

  To execute a Verilog design using VeriFormal
  1) translate the design automatically to Isabelle/HOL theory, using
   our translator. Read instructions in 'README.txt' file in 
   'Verilog-HOL translator' folder.
  2) copy and paste the text of defininition 'verimodule' from the file 'output.thy'
   created above and past it below. 

     theory output
      
 imports "../Semantic" "../Correctness" 

     begin

	  //Past the code here

     end

  3) use the command 'export_code' to export the code to OCaml
  4) copy the OCaml code of the definition 'verimodule' from the OCaml source 
    created in step 3, and replace the function of type 'program' in the 
    OCaml file 'simulate.ml' with the new design definition 'verimodule' 
   (read the 'Verilog program' section at the end of 'simulate.ml' file) 
  5) edit the definition of function 'evaluate' in 'simulate.ml' to get
   inputs and format them accordingly (remove type miss-matches between OCaml and
   Isabelle/HOL, etc...)
  6) run the 'simulate.ml'


 ********* Checking correctness of Verilog programs *********

 Use the command 'value "wfprog (verimodule)"
' inside Isabelle/HOL
 theory file created in step 2 above. A 'True' would indicate the 
 correctness of the program. 


 ********* Theorem proving **********************************
 
 Define and prove theorems in the theory created in in step 2 above
 or create another theory and import 'output.thy'. See an example
 of proof in Examples.thy (lemma mul2equiv).  


