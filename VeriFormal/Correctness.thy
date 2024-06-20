theory Correctness 
 imports Syntax
begin 

(*get names of expressions (without operator). This will be used to get names from
  lhs of assignments*)
 fun nameslhs :: "expl \<Rightarrow> name set" where
   "nameslhs Nil = {}"
 | "nameslhs (exp_name q#el) = {q} \<union> nameslhs el"
 | "nameslhs (exp_bitslice q _ _#el) = {q} \<union> nameslhs el"
 | "nameslhs (exp_bitsel q _#el) = {q} \<union> nameslhs el"
 | "nameslhs (exp_index q _#el) = {q} \<union> nameslhs el"
 | "nameslhs (_#el) = nameslhs el"

(*get names from declarations (name list) and combine them together in a set*)
 fun names :: "namel \<Rightarrow> name set" where
   "names Nil = {}"
 | "names (q#nl) = {q} \<union> names nl"

(*collect all the names in expression (with or without operator, e.g, rhs of assignment)*)
 fun nameexp :: "exp \<Rightarrow> name set" where
   "nameexp (exp_name q) = {q}"
 | "nameexp (exp_bv _ ) = {}"
 | "nameexp (exp_uop _ e) = nameexp e" 
 | "nameexp (exp_bop e1 _ e2) = nameexp e1 \<union> nameexp e2"
 | "nameexp (exp_lop e1 _ e2) = nameexp e1 \<union> nameexp e2"
 | "nameexp (exp_cop e te fe) = nameexp e \<union> nameexp te \<union> nameexp fe"
 | "nameexp (exp_rsn e _) = nameexp e"
 | "nameexp (exp_lsn e _) = nameexp e"
 | "nameexp (exp_bitslice q _ _) = {q}"
 | "nameexp (exp_bitsel q _) = {q}"
 | "nameexp (exp_index q _) = {q}"

(*get names in sensitivity list. expression can only be without operator. 
 its empty for star.*)
 fun namessl :: "sensit list \<Rightarrow> name set" where
   "namessl Nil = {}"
 | "namessl (trg_posed e#sl) = nameslhs [e] \<union> namessl sl"
 | "namessl (trg_neged e#sl) = nameslhs [e] \<union> namessl sl"
 | "namessl (trg_exp e#sl) = nameslhs [e] \<union> namessl sl" 
 | "namessl (_#sl) = {}"

(*get net (input, output, inout, wire) names from the net declarations.*)
 fun nets :: "topl \<Rightarrow> name set" where
   "nets Nil = {}"
 | "nets (top_in _ _ nl#tpl) = names nl \<union> nets tpl"
 | "nets (top_out _ _ nl#tpl) = names nl \<union> nets tpl"
 | "nets (top_io _ _ nl#tpl) = names nl \<union> nets tpl"
 | "nets (top_wire _ _ nl#tpl) = names nl \<union> nets tpl"
 | "nets (_#tpl) = nets tpl"

(*get variable (reg) names from the variable declarations.*)
 fun vars :: "topl \<Rightarrow> name set" where
   "vars Nil = {}"
 | "vars (top_reg _ _ nl#tpl) = names nl\<union>vars tpl"
 | "vars (_#tpl) = vars tpl"

(*******************************************************************************)
(**************  Checking correctness of Verilog top statements ****************)
(*******************************************************************************)

(*well-formed lhs of procedural assignment. lhs of a procedural assignment is well-formed if:
   - all names in lhs are declared of type register, and
   - there is at least one name in the lhs, and 
   - no operator is used in lhs *)
 fun wflhspa :: "topl \<Rightarrow> expl \<Rightarrow> bool" where
   "wflhspa tpl (exp_name q#Nil) = (q \<in> vars tpl)"
 | "wflhspa tpl (exp_bitslice q _ _#Nil) = (q \<in> vars tpl)"
 | "wflhspa tpl (exp_bitsel q _#Nil) = (q \<in> vars tpl)"
 | "wflhspa tpl (exp_index q _#Nil) = (q \<in> vars tpl)"
 | "wflhspa tpl (exp_name q#el) = (q \<in> vars tpl \<and> wflhspa tpl el)"
 | "wflhspa tpl (exp_bitslice q _ _#el) = (q \<in> vars tpl \<and> wflhspa tpl el)"
 | "wflhspa tpl (exp_bitsel q _#el) = (q \<in> vars tpl \<and> wflhspa tpl el)"
 | "wflhspa tpl (exp_index q _#el) = (q \<in> vars tpl \<and> wflhspa tpl el)"
 | "wflhspa _ _ = False" 

(*well-formed lhs of continuous assignment. lhs of a continuous assignment is well-formed if:
   - all names in lhs are declared of type net, and
   - there is at least one name in the lhs, and 
   - no operator is used in lhs *)
 fun wflhsca :: "topl \<Rightarrow> expl \<Rightarrow> bool" where
   "wflhsca tpl (exp_name q#Nil) = (q \<in> nets tpl)"
 | "wflhsca tpl (exp_bitslice q _ _#Nil) = (q \<in> nets tpl)"
 | "wflhsca tpl (exp_bitsel q _#Nil) = (q \<in> nets tpl)"
 | "wflhsca tpl (exp_index q _#Nil) = (q \<in> nets tpl)"
 | "wflhsca tpl (exp_name q#el) = (q \<in> nets tpl \<and> wflhsca tpl el)"
 | "wflhsca tpl (exp_bitslice q _ _#el) = (q \<in> nets tpl \<and> wflhsca tpl el)"
 | "wflhsca tpl (exp_bitsel q _#el) = (q \<in> nets tpl \<and> wflhsca tpl el)"
 | "wflhsca tpl (exp_index q _#el) = (q \<in> nets tpl \<and> wflhsca tpl el)"
 | "wflhsca _ _ = False"

(*set of all declared names.*)
 definition env :: "topl \<Rightarrow> name set" where
   "env tpl = nets tpl \<union> vars tpl" 
 
(*well-formed sensitivity list (must not be empty and all names must have been declared
 as net or variables)*)
 fun wfsl :: "topl \<Rightarrow> sensit list \<Rightarrow> bool" where
   "wfsl tpl Nil = False"
 | "wfsl tpl [trg_star] = True"
 | "wfsl tpl sl = (namessl sl \<subseteq> env tpl)"
 
(*well-formed expression (all names must have been declared as net or variables)*)
 definition wfexp :: "topl \<Rightarrow> exp \<Rightarrow> bool" where
   "wfexp tpl e = (nameexp e \<subseteq> env tpl)"

(*well-formed statement (recursive function). a statement is well-formed if: 
  - skip, finish, and disable are well-formed
  - assignments are well-formed if lhs, rhs and sensitivity lists are well-formed
  - all other statements are well-formed if statements in their body, sensitivity list
    and expressions are well-formed (case statement body must be non-empty).*)
 fun wfstm :: "topl \<Rightarrow> statement \<Rightarrow> bool" where
    "wfstm tpl (stm_dba el d e) = (wflhspa tpl el \<and> wfexp tpl e)"
  | "wfstm tpl (stm_tba el sl e) = (wflhspa tpl el \<and> wfsl tpl sl \<and> wfexp tpl e)"
  | "wfstm tpl (stm_dnba el d e) = (wflhspa tpl el \<and> wfexp tpl e)"
  | "wfstm tpl (stm_tnba el sl e) = (wflhspa tpl el \<and> wfsl tpl sl \<and> wfexp tpl e)"
  | "wfstm tpl (stm_ife e ts fs) =  (wfexp tpl e \<and> wfstm tpl ts \<and> wfstm tpl fs)"
  | "wfstm tpl (stm_while e s) = (wfexp tpl e \<and> wfstm tpl s)"
  | "wfstm tpl (stm_cb on s) = wfstm tpl s"
  | "wfstm tpl (stm_case e [cs] ds) = (wfexp tpl e \<and> wfstm tpl ds \<and> wfstm tpl (snd cs))"
  | "wfstm tpl (stm_case e (cs#lcs) ds) = 
      (wfstm tpl (snd cs) \<and> wfstm tpl (stm_case e lcs ds))"  
  | "wfstm tpl (stm_case e Nil ds) = False"
  | "wfstm tpl (stm_sensl sl s) = (wfsl tpl sl \<and> wfstm tpl s)"
  | "wfstm tpl (stm_delay d s) = wfstm tpl s"
  | "wfstm tpl (stm_seq s1 s2) = (wfstm tpl s1 \<and> wfstm tpl s2)"
  | "wfstm tpl _ = True"

(*whether or not a statement is/contain timing control. To be used in checking validity of always 
 statement. *)
fun hastimectrl :: "statement \<Rightarrow> bool" where
   "hastimectrl (stm_sensl _ _) = True"
 | "hastimectrl (stm_delay _ _) = True"
 | "hastimectrl _ = False"
                               

(*well-formed Verilog top statements. a top statement is well-formed if:
  - net declaration is well-formed if names are not declared as variable
    (reg) before. (a net identifier, though, can be declared multiple times
    (e.g., as input and wire)). 
  - all the variables declared as input or inout are included in the ports list of the module. 
  - variable declaration is well-formed if the names are not declared (as net or var) before.
  - continuous assignment is well-formed if lhs and rhs are well-formed
  - initial and always are well-formed if their bodies are well-formed. 
 Note: first argument of wftop in recursive calls is the list of top statements seen so far. 
      It must be provided empty when called (e.g.,in wfprog function) *)
 fun wftop :: "topl \<Rightarrow> topl \<Rightarrow> namel \<Rightarrow> bool" where
   "wftop tpl Nil _ = True"
 | "wftop tpl (top_in n2 n1 nl#tpl') pl = (nl \<noteq> Nil \<and> names nl \<subseteq> names pl \<and>
       n2 \<ge> n1 \<and> (vars tpl \<inter> names nl = {}) \<and> wftop (top_in n2 n1 nl#tpl) tpl' pl)" 
 | "wftop tpl (top_out n2 n1 nl#tpl') pl = (nl \<noteq> Nil \<and> 
       n2 \<ge> n1 \<and> (vars tpl \<inter> names nl = {}) \<and> wftop (top_out n2 n1 nl#tpl) tpl' pl)" 
 | "wftop tpl (top_io n2 n1 nl#tpl') pl = (nl \<noteq> Nil \<and> names nl \<subseteq> names pl \<and>
       n2 \<ge> n1 \<and> (vars tpl \<inter> names nl = {}) \<and> wftop (top_io n2 n1 nl#tpl) tpl' pl)" 
 | "wftop tpl (top_wire n2 n1 nl#tpl') pl = (nl \<noteq> Nil \<and>
       n2 \<ge> n1 \<and> (vars tpl \<inter> names nl = {}) \<and> wftop (top_wire n2 n1 nl#tpl) tpl' pl)" 
 | "wftop tpl (top_reg n2 n1 nl#tpl') pl = (nl \<noteq> Nil \<and>
       n2 \<ge> n1 \<and> (env tpl \<inter> names nl = {}) \<and> wftop ((top_reg n2 n1 nl)#tpl) tpl' pl)" 
 | "wftop tpl (top_assign d el e#tpl') pl = (wflhsca tpl el \<and> wfexp tpl e \<and> wftop tpl tpl' pl)"
 | "wftop tpl (top_initial s#tpl') pl = (wfstm tpl s \<and> wftop tpl tpl' pl)"  
 | "wftop tpl (top_always s#tpl') pl = (wfstm tpl s \<and> wftop tpl tpl' pl)"      

(*******************************************************************************)
(********************  Checking correctness of ports  **************************)
(*******************************************************************************)

(*well-formed program. a program is well-formed if:
  - body is not empty, and
  - all top statements are well-formed. *)
 fun wfprog :: "program \<Rightarrow> bool" where
   "wfprog (prog_mod pl tpl) = (tpl \<noteq> [] \<and> wftop [] tpl pl)"
 

end