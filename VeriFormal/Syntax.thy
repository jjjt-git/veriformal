(* Verilog syntax *)

theory Syntax
 imports Bitvector (* Main "~~/src/HOL/Word/Word" *)  
begin 

 (*identifiers 
 typedecl name*)

 datatype name = 
  X | Y | Z | CLK | I1 | O1 | R1 | R2  | R3 | R4 | R5 | W1 | W2 | W3 | W4
  | sum_out | carry_out | carry_in | ina | inb 
  | bus_out | bus0 | bus1 | bus2 | enable | select | data |
   one | two |  three |  four 
  |  i1 |  o1 |  w1 |  i2 |  o2 | Xi | Yi 
  | Q | Q' | R | S 

(*
 datatype exp = 
   exp_name name   ("\<^sub>n_")
 | exp_sum exp exp
 | exp_sub exp exp  

 term "exp_sum (exp_sub (\<^sub>nX) (\<^sub>nY)) \<^sub>nZ"

  datatype exp' = 
   exp_name' name   ("\<^sub>n_")
 | exp_sum' exp' fact
 | exp_sub' exp' fact
 and 
   fact = exp_fact exp'
*)

 type_synonym namel = "name list"

 datatype exp = 
   exp_name name        ("\<^sub>n_")
 | exp_bv bitvector     ("\<^sub>v_")
 | exp_uop uop exp      ("\<^sub>u_ _")
 | exp_bop exp bop exp  ("\<^sub>b_ _ _")
 | exp_lop exp lop exp  ("\<^sub>l_ _ _")
 | exp_cop exp exp exp  ("\<^sub>c_ _ _")         (*conditional operator*)
 | exp_rsn exp nat      ("_ [>>] _") 
 | exp_lsn exp nat      ("_ [<<] _")
 | exp_bitslice name nat nat   ("\<^sub>p_[_:_]") (*bit part (slice) Q[4:2] with exp_id_name Q n2 n1, with n2 being 4*)
 | exp_bitsel name nat         ("\<^sub>s_[_]")   (*do we need this? if there is 'exp_nat nat', then no*)
 | exp_index name exp          ("\<^sub>i_[_]")
 
term "\<^sub>pR2 [3 : 0]"
term "\<^sub>b\<^sub>nR2 [+] \<^sub>v(1, 4)"

 term "\<^sub>nR1" 


 type_synonym expl = "exp list"
 type_synonym env = "(name * bitvector) list" (*as set?*)

(*sensitivity list. exp is used to check polarity or change of a single bit and bit slice,
 in addition, to checking the whole value of [bitvector] stored in a variable.*)
 datatype sensit =
    trg_star        ("\<star>")
  | trg_posed exp   ("posedge _")
  | trg_neged exp   ("negedge _")
  | trg_exp exp    ("trgexp _")

 type_synonym sensl = "sensit list"

(*statements *)
 datatype statement = 
   stm_skip
 | stm_finish                ("$finish")
 | stm_disab name            ("disable _")
 | stm_dba expl int exp      ( "_ [=] [#] _ _" )  (*non/delayed blocking assign*)
 | stm_tba expl sensl exp    ("_ [=] [@](_) _")   (*triggered blocking assign*)
 | stm_dnba expl int exp     ( "_ [=<] [#] _ _" ) (*non/delayed non-blocking assign*)
 | stm_tnba expl sensl exp   ("_ [<=] [@](_) _")  (*triggered non-blocking assign*)
 | stm_ife exp statement statement  ("IF _ THEN _ ELSE _")
 | stm_while exp statement          ("WHILE (_) _")       (*While loop, should be used to model repeat, forever, and for loops*)
 | stm_cb "name option" statement  ("BEGIN : [_] _ END")    (*named/un-named code block, e.g. begin: .. end*)
 | stm_case exp "(exp*statement) list" statement   ("CASE (_) _ DEFAULT : _ ENDCASE")
 | stm_sensl sensl statement   ("[@](_)_")  
 | stm_delay nat statement     ("[#] _ _")
 | stm_seq statement statement (infixr ";;" 30)   

 term "IF \<^sub>nR1 THEN stm_seq ([\<^sub>nR1] [=] [#] -1  \<^sub>nR1) ([\<^sub>nR1] [=] [#] -1  \<^sub>nR1) ELSE stm_skip"

 term "IF \<^sub>nR1 THEN ([\<^sub>nR1] [=] [#] -1  \<^sub>nR1);;([\<^sub>nR1] [=] [#] -1  \<^sub>nR1) ELSE stm_skip"

 type_synonym stml = "statement list"

 text{*"If a signal on a sensitivity changes according to its prescribed polarity, the
  procedural block is triggered. On the other hand, if a signal changes that is not on 
  the sensitivity list but is present in the right-hand side of some procedural statements 
  of the block, the procedural statements will not be updated."*}

 
(*top_assign represents continuous assignments. The assignment occurs
whenever simulation causes the value of the right-hand side to change*)
 datatype top = 
   top_in nat nat namel     ("input [_:_] _")         (*scalar? 0 0 can represent that*) 
 | top_out nat nat namel    ("output [_:_] _")
 | top_io nat nat namel     ("inout [_:_] _")         (*bi-directional data bus*)
 | top_wire nat nat namel   ("wire [_:_] _")
 | top_reg nat nat namel    ("reg [_:_] _")
 | top_assign int expl exp  ("assign #_ _ = _")   (*non/delayed cont assign, with tuples on lhs*)
 | top_initial statement    ("initial _")          (*stm_cb, would be used to  model code block*)
 | top_always statement     ("always _")          (*trigger stm to  model trigger part and then the code block*)
 
 type_synonym topl = "top list" 

(*NOTE:The always statement should contain at least one procedural timing control.*)

(*modules are connected by ports (input, output or inout). *)
 datatype program  = 
  prog_mod "name list" topl   ("module (_) _ endmod") 

(*Rules for connecting ports:
 Input Ports: Internally the input ports must always be of type net. Externally the inputs
    can connect to a variable of type reg or net.
 Outputs: Internally output port can be net or reg. Externally the outputs must connect to
    a variable of type net.
 Inouts: The Inout port must always be of type net internally or externally .
*)     

(* NOTES:
 always block can not drive (e.g. used at lhs of assignment) wire data type but
  can drive reg and integer data types.
*)

(*processes (computations)*)
 datatype process =
    cpt_stm statement         (*statements*)
  | cpt_alw sensl process     (*Verilog top statements*)
  | cpt_dca int expl exp exp  (*delay, lhs, rhs, rhs value*)

(*Note: cont assigns may add future events, which are dealt with differently than other
 future events. They could be dealt with as pure always block with [cpt_alw] inside body, 
 however, a hybrid approach is taken here: inside always block, instead, [cpt_dca] is used 
 to store the assign part of cont assign. it is needed when 'canceling' is implemented for
 net assigns scheduled at future time. the assignment part, though, is modeled as blocking
 assignment. the first three arguments models the assignment [assign #d {x, y} = rhs_exp] and 
 the last [exp] stores the value of rhs expression. This is needed to store both the value of
 rhs evaluated after trigger and the original rhs body for converting the process
 back to listening event. TODO: It needs to by modified when blocking assignments are changed
 to only reg variables on lhs (as cont assign only drives nets). *)

(*events.*)
 datatype event = 
     evt_upd exp bitvector          (*update events (e.g. by blocking assigns)*)
   | evt_updl "event list" process  (*list of update events in a procedural block*)
   | evt_inact process              (*in-active events*)
   | evt_fut nat process            (*future events (to happen at simulation cycle n)*)
   | evt_listn sensl process        (*listening events (waiting for a trigger in sensitivity list)*)
 
(*NOTE: in [evt_upd] the first parameter can not be [name] as it looses information about bitselect
 or bitslice, which is needed when the event is later executed (e.g. in case of non-blocking assign
 the event is stored as non-blocking assign update event, which is processed at the end of each
 simulation cycle. 
 The difference between [evt_upd] and [evt_cupd] is the way they activate listening events.
 Continuous updates activate events when the value changes, while the other, in addition, takes
 polarity change (edges) in consideration.*)

(*NOTE: event [evt_updl] is used to combine events that need to be executed in order (e.g., 
 all the events of a procedural assignment with tuple on lhs, or all non-blocking assignments
 in a procedure). In our case, all of the events created for a tuple of blocking assignment are
 executed immediately without storing them in update events. currently, only update events created
 for non-blocking assignments are stored in non-blocking assign update events, which are eventually
 combined in a single [evt_updl] even. As non-blocking assign update events is a list, there is 
 actually no need of [evt_updl] and instead the event can be stored as update events when they 
 are being executed (after inactive events). However, [evt_upld] it is left as it may be needed
 in future.*)

(*Verilog program configuration*)
 record configuration = 
   cfg_env :: env
   cfg_time :: nat
   cfg_actp :: "process list"
   cfg_upde :: "event list"
   cfg_inacte :: "event list"
   cfg_nbaue :: "event list"
   cfg_fute :: "event list"
   cfg_listne :: "event list"
   cfg_disabs :: "name set"
   cfg_finish :: bool

text{*"When multiple processes are triggered at the same time, the order 
  in which the processes are executed is not specified by Institute of 
  Electrical and Electronics Engineers (IEEE) standards. Thus, it is 
  arbitrary and it varies from simulator to simulator. This phenomenon is
  called nondeterminism." Active processes are, therefore, modeled as a set
  (lists are easy to deal with, so we are using list instead).
  The processing of all the active events is called a simulation cycle.*}

(*initial program configuration*)
 definition initconfig :: configuration where
   "initconfig \<equiv> \<lparr> 
     cfg_env = Nil, 
     cfg_time = 0,
     cfg_actp = [],
     cfg_upde = [],
     cfg_inacte = [],
     cfg_nbaue = [],
     cfg_fute = [], 
     cfg_listne = [],
     cfg_disabs = {},
     cfg_finish = False
   \<rparr>"

end