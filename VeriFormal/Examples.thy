theory Examples
 imports Semantic Correctness 
begin

(**************************************************************************************)
(************************* Type checking programs *************************************)
(**************************************************************************************)
 
 definition incorrect :: program where
  "incorrect \<equiv>
  module ([])
  [
    reg [4:0] [X],
    wire [4:0] [Y],

    assign # -1 [\<^sub>nY] = \<^sub>b\<^sub>nX [+] \<^sub>v(1, 4),

    initial
     BEGIN : [None]
       ([\<^sub>nX] [=] [#] -1 \<^sub>v(1,4))
     END,

    always ([@]([trg_exp \<^sub>sX[0]])
      BEGIN : [None]
       ([\<^sub>nX] [=] [#]-1 \<^sub>b\<^sub>nX [+] \<^sub>v(1, 4))
      END)
  ]
  endmod
 " 
  
 value "wfprog incorrect"   (*variable is not allowed in LHS of continuous assignments. *)

lemma test: "wfexp [top_in n2 n1 [q]] (exp_name q)" 
   apply (simp add: wfexp_def env_def) 
 done


(******** Other examples of VeriFormal descriptions ********)

definition fulladder :: "nat \<Rightarrow> program" where
  "fulladder len =
  module ([sum_out, carry_out, carry_in, ina, inb])
  [
    output [len:0] [sum_out],
    input [len:0] [ina, inb],
    output [0:0] [carry_out],
    input [0:0] [carry_in],
   
    assign # -1 [\<^sub>nsum_out, \<^sub>ncarry_out] = \<^sub>b \<^sub>nina [+] \<^sub>b \<^sub>ninb [+] \<^sub>ncarry_in 
  ]
 endmod
 "

value "simulate 1 (fedinput [(carry_in, 0), (ina, 5), (inb, 3)]
        (state (fulladder 4)))" 

value "wfprog (fulladder n)"

 
(*if enable bit is high (1), then select value connects (chooses) input bus to the
 output bus (bus_out).[selectbus bus_len, bus 1, bus 2, enable bit, select bus]. 
 execution order of the listening events is preserved. *)
definition selectbus :: program where
  "selectbus =
  module ([bus_out, bus1, bus2, enable, select])
  [
    output [3:0] [bus_out],
    input [3:0] [bus1,bus2],
    wire [3:0] [data],
    input [0:0] [enable],
    input [1:0] [select],
   
    assign # -1 [\<^sub>nbus_out] = \<^sub>c \<^sub>nenable \<^sub>ndata \<^sub>v(0, 4), 

    assign # -1 [\<^sub>ndata] = \<^sub>c \<^sub>l \<^sub>nselect [==] \<^sub>v(1, 2) \<^sub>nbus1 \<^sub>v(0, 4),
    assign # -1 [\<^sub>ndata] = \<^sub>c \<^sub>l \<^sub>nselect [==] \<^sub>v(2, 2) \<^sub>nbus2 \<^sub>v(0, 4)
  ]
 endmod 
 "    

definition mulbyprod:: "int \<Rightarrow> program" where
 "mulbyprod x = 
  module ([])
  [
    wire [3:0] [R1],
 
    assign # -1 [\<^sub>nR1] = \<^sub>b\<^sub>v(x, 4) [*] \<^sub>v(2, 4)
  ]
  endmod
 "

 value "simulate 1 (fedinput [] (state (mulbyprod 3)))"

	definition mulbyshift:: "int \<Rightarrow> program" where
	 "mulbyshift x = 
	  module ([])
	  [
		wire [3:0] [R1],
	 
		assign # -1 [\<^sub>nR1] = ((\<^sub>v(x, 4)) [<<] 1)
	  ]
	  endmod
	 "

value "simulate 0 (fedinput [] (state (mulbyshift 3)))"
 
lemma mul2equiv [simp]: "simulate 0 (fedinput [] (state (mulbyshift 3))) = simulate 0 (fedinput [] (state (mulbyprod 3)))" 
  apply (simp add: stepsim_def mulbyshift_def mulbyprod_def mkconfig_def initconfig_def
       state_def processba_def updateconfig_def nextcycleb_def nextpassb_def updatevar_def slicebv_def maskn_def
       binopbv_def Let_def shiftl_int_def bvlsn_def)
  done

(*module instantiation example*)
definition verimodule :: program where 
 "verimodule = 
module ([i1, o1])

[input [0:0] [i1],
output [0:0] [o1],
wire [0:0] [w1],

assign # -1 [\<^sub>n i2]=\<^sub>n i1,
input [0:0] [i2],
output [0:0] [o2],

assign #1 [\<^sub>n o2]=\<^sub>n i2,

assign # -1 [\<^sub>n w1]=\<^sub>n o2]

endmod
"

(*VeriCert and Iverilog outputs*)
definition addintalw :: program where 
 "addintalw = 
module ([Xi, Yi])

[input [7:0] [Xi,Yi],
wire [7:0] [X,Y],
reg [7:0] [Z],

assign #0 [\<^sub>n X]=\<^sub>n Xi,

assign #0 [\<^sub>n Y]=\<^sub>n Yi,

always ( [#]2 BEGIN : [None]
([\<^sub>n Z] [=] [#] -1 (\<^sub>b \<^sub>n X [+] \<^sub>n  Y));;( $finish)
END )]

endmod
"
value "simulate 2 (fedinput [(Xi, 2), (Yi, 5)] (state addintalw))" 

definition evaluate :: int where
  "evaluate =  
    (let C = (simulate 2 (fedinput [(Xi, 2), (Yi, 5)] (state addintalw))) in 
    fst(getbvenv Z (cfg_env C) )) "  


definition latch:: program where 
 "latch = 
module ([Q, Q', S, R])
[
 output [0:0] [Q,Q'], 
 input [0:0] [S,R],
 reg [0:0] [Q,Q'],


 initial 
  BEGIN : [None]
    ([\<^sub>nQ] [=] [#]-1 \<^sub>v(0,1));;
    ([\<^sub>nQ'] [=] [#]-1 \<^sub>v(1,1))
  END,


 always ( [#]0
 BEGIN : [None]
  CASE (\<^sub>nS)
   [(\<^sub>v(0,1), 
       (IF (\<^sub>l \<^sub>nR [==] \<^sub>v(0,1))     
        THEN (([\<^sub>nQ] [=] [#]-1 \<^sub>nQ);;([\<^sub>nQ'] [=] [#]-1 \<^sub>nQ'))            (*S=0, R=0*)
        ELSE (([\<^sub>nQ] [=] [#]-1 \<^sub>v(0,1));;([\<^sub>nQ'] [=] [#]-1 \<^sub>v(1,1))))),  (*S=0, R=1*)
    (\<^sub>v(1,1),
       (IF (\<^sub>l \<^sub>nR [==] \<^sub>v(0,1))
        THEN (([\<^sub>nQ] [=] [#]-1 \<^sub>v(1,1));;([\<^sub>nQ'] [=] [#]-1 \<^sub>v(0,1)))     (*S=1, R=0*)
        ELSE $finish))  (*undefined*)                               (*S=1, R=1*)
   ]
   DEFAULT :$finish
  ENDCASE
 END) 
]
endmod
"
value "state latch"

value "simulate 2 (fedinput [(S, 1), (R, 0), (CLK, 0)] (state latch))" 

export_code evaluate in OCaml
   module_name Evaluate file "simulate.ml"


end


