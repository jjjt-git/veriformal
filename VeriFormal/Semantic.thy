theory Semantic
 imports Syntax BasicDefinitions HOL.Finite_Set
begin 

(**************************** Evaluating expressions **************************************)
 
(*big-step operational semantics for expressions.*)
 primrec evalexp :: "env \<Rightarrow> exp \<Rightarrow> bitvector" where
   "evalexp en (exp_name q) = getbvenv q en"  (*variable lookup*)
 | "evalexp en (exp_bv v) = v" 
 | "evalexp en (exp_uop opr e') = unopbv opr (evalexp en e')"
  (*NOTE EDIT: This was mistakenly published before as the following. The following case
    does not evaluate unary operation on expression other than bit-vector. *)
  (*  (case e' of  
      exp_bv v \<Rightarrow> unopbv opr v
    | _ \<Rightarrow> evalexp en e')"  *)
 | "evalexp en (exp_bop e1 opr e2) =
     binopbv (evalexp en e1) opr (evalexp en e2)"
 (* NOTE EDIT: The following cases were replaced with the above one life. expressions are 
   evaluated by the recursive calls, anyway.
   (case (e1, e2) of   
     (exp_bv v1, exp_bv v2) \<Rightarrow> binopbv v1 opr v2
   | (exp_bv v1, _) \<Rightarrow> binopbv v1 opr (evalexp en e2)
   | (_, exp_bv v2) \<Rightarrow> binopbv (evalexp en e1) opr v2
   | (_, _) \<Rightarrow> binopbv (evalexp en e1) opr (evalexp en e2))" *)
 | "evalexp en (exp_lop e1 opr e2) = lopbv (evalexp en e1) opr (evalexp en e2) "
 | "evalexp en (exp_cop e te fs) = 
    (if (fst(evalexp en e) = 1) then (evalexp en te) else (evalexp en fs))"
 | "evalexp en (exp_rsn e' n) = bvrsn (evalexp en e') n"
   (*NOTE EDIT: This was mistakenly published before as the following. The following case
    does not evaluate right-shift operation on expression other than bit-vector. *)
  (* (case e' of 
     exp_bv v \<Rightarrow> bvrsn v n
   | _ \<Rightarrow> evalexp en e')" *)
 | "evalexp en (exp_lsn e' n) = bvlsn (evalexp en e') n"
  (*NOTE EDIT: This was mistakenly published before as the following. The following case
    does not evaluate left-shift operation on expression other than bit-vector. *)
  (* (case e' of 
     exp_bv v \<Rightarrow> bvlsn v n
   | _ \<Rightarrow> evalexp en e')" *)
 | "evalexp en (exp_bitslice q n2 n1) = slicebv (getbvenv q en) n2 n1"
 | "evalexp en (exp_bitsel q n) = slicebv (getbvenv q en) n n"
 | "evalexp en (exp_index q e) = (let index = nat (fst (evalexp en e)) in
     slicebv (getbvenv q en) index index )"
 
value "evalexp [(R1, (2, 2)), (R2, (4, 2))] (\<^sub>b\<^sub>nR2 [+] \<^sub>b\<^sub>nR2 [+] \<^sub>v(0, 4))"
value "evalexp [(R1, (2, 4))] ((\<^sub>v(2, 4)) [<<] 1)"
value "evalexp [(R1, (2, 4))] (exp_lsn (\<^sub>nR1) 1)" 

value "evalexp [(X, (2, 2)), (Y, (4, 2)), (Z, (3,2))] (\<^sub>b \<^sub>nX [+] \<^sub>l \<^sub>nY [<] \<^sub>nZ)" (*X + (Y < Z) *)
value "evalexp [(X, (2, 2)), (Y, (4, 2)), (Z, (3,2))] (\<^sub>l \<^sub>b \<^sub>nX [+] \<^sub>nY [<] \<^sub>nZ)" (*(X + Y) < Z *)

term "\<^sub>b\<^sub>nR2 [+] \<^sub>b\<^sub>nR2 [+] \<^sub>v(1, 4)"

 (*size of variable on lhs of the assignment*)
 fun sizeoflhs :: "env \<Rightarrow> exp \<Rightarrow> nat" where
   "sizeoflhs en (exp_name q) = snd(getbvenv q en)"
 | "sizeoflhs en (exp_bitslice q n2 n1) = (n2 - n1) + 1"
 | "sizeoflhs en (exp_bitsel q n) = 1"
 | "sizeoflhs en (exp_index q e') = 1"
 | "sizeoflhs en _ = 0"

 (*size for the assignment operation expl [= or <=] exp: max of the sum of sizes in tuple (expl) 
  on lhs and size of exp on rhs (exp). right most variable in the tuple (in Verilog, it is written
  as a set) is at the head of the list*)
 definition sizeofexp:: "expl \<Rightarrow> env \<Rightarrow> exp \<Rightarrow> nat" where
 "sizeofexp el en e =  max (fold plus (map (sizeoflhs en) el) 0) (snd(evalexp en e))"

(************************* Calculating length of statements and processes ********************)

(*these functions are needed for termination of recursive functions*)

(*length of statement. [stm_seq s1 s2] is equal sum of len s1 + len s2 + 1, because
 the function [execp] first parses the sequence and then processes s1 and s2.*)
 fun lenstm :: "env \<Rightarrow> statement \<Rightarrow> nat" where
   "lenstm en (stm_seq k1 k2) = 1 + (lenstm en k1 + lenstm en k2)"
 | "lenstm en (stm_cb on s) = lenstm en s"
 | "lenstm en (stm_ife e ts fs) =      
     (if (fst (evalexp en e)) = 1 then (lenstm en ts) else (lenstm en fs))"
    (* max (lenstm en ts) (lenstm en fs)" The line below was replaced with above one AFTER an error in termination functions was
      found. See 'Error log' file for more detail. *)
 | "lenstm en (stm_while e s) = 
     (if (fst (evalexp en e)) = 1 then (lenstm en s) else 1)"  (*While is executed only ONCE*)
 | "lenstm en _ = 1"


 (*count computations that makes a process*)
 fun countcpt :: "env \<Rightarrow> process \<Rightarrow> nat" where
    "countcpt en (cpt_stm s) = lenstm en s"
  | "countcpt en (cpt_alw sl k) = countcpt en k"
  | "countcpt en (cpt_dca _ _ _ _) = 1" 

 (*convert listening event to an always process*)
 definition letoproc:: "event \<Rightarrow> process" where
  "letoproc ev = (case ev of 
    evt_listn sl (cpt_dca sl' d el e) \<Rightarrow> cpt_dca sl' d el e
  | evt_listn sl K \<Rightarrow> cpt_alw sl K
  | _ \<Rightarrow> cpt_stm stm_skip
 )"

 (*count computations in listening event list*)
 fun countcptel :: "env \<Rightarrow> event list \<Rightarrow> nat" where
  "countcptel en el = (case el of
     [] \<Rightarrow> 0
   | (e#el') \<Rightarrow> countcpt en (letoproc e) + countcptel en el')"

 (*count computations in list of processes*)
 fun countcptpl :: "env \<Rightarrow> process list \<Rightarrow> nat" where
  "countcptpl en pl = (case pl of
     Nil \<Rightarrow> 0
   | p#pl' \<Rightarrow> countcpt en p + (countcptpl en pl'))"

(********************** Make list/set of events for assigns tuples ***************************)

(*makes a (list for tuples) of update events. each update event stores lhs expression (name) and 
 a [bitvector], and for the next lhs expression (name), the [bitvector] is shifted right according
 to size of the slice to position next sequence of bits for next variable in the lhs tuple. later,
 when update event is executed, the corresponding bit(s) are updated in bitvector value stored
 with variable name according to the expression of each event (see [updatevar] function).*) 
 fun mkuevents:: "env \<Rightarrow> expl \<Rightarrow> bitvector \<Rightarrow> event list" where
 "mkuevents en el bv = (case el of
    [] \<Rightarrow> [] 
  | (e#el') \<Rightarrow> (case e of 
      exp_name q \<Rightarrow> (evt_upd e bv)#(mkuevents en el' (bvrsn bv (snd(getbvenv q en)))) 
    | exp_bitslice q n2 n1 \<Rightarrow> (evt_upd e bv)
                              #(mkuevents en el' (bvrsn bv ((n2-n1)+1)))
    | exp_bitsel q n \<Rightarrow> (evt_upd e bv)#(mkuevents en el' (bvrsn bv 1))
    | exp_index q e' \<Rightarrow> (evt_upd e bv)
                        #(mkuevents en el' (bvrsn bv 1))
    | _ \<Rightarrow> mkuevents en el' bv
    )
  )"   

 (*add (name, value) pair to environment. update value if variable is already existed*)
 fun addbinding :: "env \<Rightarrow> (name * bitvector) \<Rightarrow> env" where
   "addbinding [] b = [b]"
 | "addbinding (p#pl) b = (if (fst(p)) = (fst(b)) then (b#pl) else p#addbinding pl b) " 

 (*update variable value (replace all, slice, or a bit) (processing update events)*)
 definition updatevar :: "env \<Rightarrow> exp \<Rightarrow> bitvector \<Rightarrow> env" where
 "updatevar en e bv = (case e of 
      exp_name q \<Rightarrow> addbinding en (q, (slicebv bv (snd(getbvenv q en) - 1) 0))
    | exp_bitslice q n2 n1 \<Rightarrow> addbinding en (q, (slicebva (getbvenv q en) bv n2 n1))
    | exp_bitsel q n \<Rightarrow> addbinding en (q, (slicebva (getbvenv q en) bv n n))
    | exp_index q e' \<Rightarrow> addbinding en (q, (slicebva (getbvenv q en) bv (nat(fst(evalexp en e'))) (nat(fst(evalexp en e'))) ))
    | _ \<Rightarrow> en
  )"   

(**********************  Update environment **************************************************)
(*add a variable (initialized with 0) to environment. TODO: it should be x or z, 
 when trisate is implemented *)
 fun addavar:: "env \<Rightarrow> namel \<Rightarrow> nat \<Rightarrow> env" where
   "addavar en (q # nl') l = [(q, (0,l))]@(addavar en nl' l)"
 | "addavar en [] l = en"
 
 fun updateenv:: "env \<Rightarrow> top \<Rightarrow> env" where
   "updateenv en (top_in n2 n1 nl) = addavar en nl ((n2 - n1) + 1)"
 | "updateenv en (top_out n2 n1 nl) = addavar en nl ((n2 - n1) + 1)"
 | "updateenv en (top_io n2 n1 nl) = addavar en nl ((n2 - n1) + 1)"
 | "updateenv en (top_reg n2 n1 nl) = addavar en nl ((n2 - n1) + 1)"
 | "updateenv en (top_wire n2 n1 nl) = addavar en nl ((n2 - n1) + 1)"
 | "updateenv en _ = []"
 

(*NOTE: recursive functions should be defined as recursive using [fun] with equations. 
 With a recursive function f using equation for each constructor, 
 a customised inductive rule f.induct is derived, which simplify 
 inductive proofs using tactic [apply (induction n rule: f.induct)]*)

(*generates a process from top initial and always (with delay) statement. the always 
 statement should contain at least one procedural timing control. always with sensitivity
 is added as a listening event. see next functions.*)
 fun toptoproc:: "top \<Rightarrow> process" where
   "toptoproc (top_initial s) = cpt_stm s" 
 | "toptoproc _ = cpt_stm stm_skip"  (*Often generates un-necessary stm_skip statements *)
 
(*Note: the following three functions assumes, there is no variable in the rhs of 
 cont assignment. based on the value of delay, either update, inactive or future
 event is generated. cont assign with variable(s) on rhs are first converted to
 listening (on rhs variables) events (by function [toptolcle]), and then to any of
 the above event types based on the delay value.*)

(*converts cont assign to (list of, if tupes on lhs) cont update events*)
 fun toptocu:: "env \<Rightarrow> top \<Rightarrow> event list" where
   "toptocu en (top_assign d el e) = (if senslexp e = [] \<and> d < 0
          then mkuevents en el (evalexp en e) else [])"
 | "toptocu _ _ = []"

(*converts cont assign to an inactive event, with assignment part as cont assignment process. *)
 fun toptoinact:: "env \<Rightarrow> top \<Rightarrow> event list" where
   "toptoinact en (top_assign d el e) = (if senslexp e = [] \<and> d = 0 then
          [evt_inact (cpt_dca (-1) el e e)] else [])"
 | "toptoinact en (top_always (stm_delay 0 s)) = [evt_inact (cpt_stm s)]" 
 | "toptoinact _ _ = []"

(*
 "execstm (stm_delay n s) C = (if n = 0
         then (C\<lparr>cfg_inacte := (cfg_inacte C)@[evt_inact (cpt_stm s)]\<rparr>)
         else (C\<lparr>cfg_fute := addevent (evt_fut (n + (cfg_time C)) (cpt_stm s)) (cfg_fute C)\<rparr>) )"
*)


(*converts cont assign to future event (sorted by time), if there is no variable on rhs, with
 assignment part as cont assignment process.*)
 fun toptofut :: "nat \<Rightarrow> top list \<Rightarrow> event list" where
    "toptofut _ Nil = Nil"
  | "toptofut tm ((top_assign d el e)#tpl) =
       (if senslexp e = [] \<and> d > 0
       then addevent (evt_fut (nat(d) + tm) (cpt_dca (-1) el e e)) (toptofut tm tpl)
       else (toptofut tm tpl))"
  | "toptofut tm ((top_always (stm_delay (Suc n) s))#tpl) = addevent (evt_fut (Suc n + tm) (cpt_stm s)) (toptofut tm tpl)"
  | "toptofut tm (_#tpl) = toptofut tm tpl"  

(*converts always and cont assign in program to list of listening events. An always is
 registered once as a listening event, and cont assign is also dealt with as if it was an
 always block, with sensit list made from variables on rhs and cont assign computation in
 its body.*)
 fun toptole:: "top list \<Rightarrow> event list" where
  "toptole tpl = (case tpl of
    Nil \<Rightarrow> []
  | tp#tpl' \<Rightarrow> (case tp of
        top_assign d el e  \<Rightarrow> 
          (case senslexp e of
            (s#sl) \<Rightarrow> [evt_listn (s#sl) (cpt_dca d el e e)]@toptole tpl'
          | Nil \<Rightarrow> toptole tpl')
      | top_always (stm_sensl sl s) \<Rightarrow>  let sl' = (if sl = [trg_star] then (senslstm s) else sl)
        in [evt_listn sl' (cpt_stm s)]@toptole tpl'
      | _ \<Rightarrow> toptole tpl')
   )"

(*Add bindings, processes, cont update, cont listening, inactive and future events to 
 initial configuration *)
 definition mkconfig:: "topl \<Rightarrow> configuration" where
  "mkconfig tpl = (case tpl of 
    Nil \<Rightarrow> initconfig      
  | _ \<Rightarrow> let en = fold append (map (updateenv []) tpl) [] in
     (initconfig 
       \<lparr>cfg_env := en,
       cfg_actp := map toptoproc tpl,
       cfg_upde := fold append (map (toptocu en) tpl) [], 
       cfg_listne := toptole tpl,
       cfg_inacte := fold append (map (toptoinact en) tpl) [],
       cfg_fute := toptofut 0 tpl
       \<rparr>)
  )"

(*****************************************************************************************)
(************************* Processing Update Events ****************** *******************)
(*****************************************************************************************)

(*********************** Activating listening events *************************************)

(*if updated variable matches a name in sensitivity list of the listening event and the 
 value of a specific bit, slice or the whole value changes,the event is triggered. the 
 function assumes the old and new values of the variable are different (when called from
 [processue]). slice bv 0 0 returns LSB bit of bv, meaning, q is a scalar (single bit,
 e.g. clock) *)
 definition letriger :: "env \<Rightarrow> name \<Rightarrow> bitvector \<Rightarrow> bitvector \<Rightarrow> sensit \<Rightarrow> bool" where
  "letriger en q1 bvold bvnew trg = (case trg of 
      trg_posed e \<Rightarrow> (case e of 
         exp_bitsel q2 n \<Rightarrow> (fst(slicebv bvold n n) < fst(slicebv bvnew n n)) \<and> (q1 = q2)
       | exp_index q2 e' \<Rightarrow> let n = nat (fst (evalexp en e')) in 
           (fst(slicebv bvold n n) < fst(slicebv bvnew n n)) \<and> (q1 = q2)
       | exp_name q2 \<Rightarrow> (fst(slicebv bvold 0 0) < fst(slicebv bvnew 0 0)) \<and> (q1 = q2)
       | _ \<Rightarrow> False)
    | trg_neged e \<Rightarrow>(case e of 
         exp_bitsel q2 n \<Rightarrow> (fst(slicebv bvold n n) > fst(slicebv bvnew n n)) \<and> (q1 = q2)
       | exp_index q2 e' \<Rightarrow> let n = nat (fst (evalexp en e')) in 
           (fst(slicebv bvold n n) > fst(slicebv bvnew n n)) \<and> (q1 = q2)
       | exp_name q2 \<Rightarrow> (fst(slicebv bvold 0 0) > fst(slicebv bvnew 0 0)) \<and> (q1 = q2)
       | _ \<Rightarrow> False)
    | trg_exp e \<Rightarrow> (case e of 
         exp_bitsel q2 n \<Rightarrow> (fst(slicebv bvold n n) \<noteq> fst(slicebv bvnew n n)) \<and> (q1 = q2)
       | exp_index q2 e' \<Rightarrow> let n = nat (fst (evalexp en e')) in 
           (fst(slicebv bvold n n) \<noteq> fst(slicebv bvnew n n)) \<and> (q1 = q2)
       | exp_bitslice q2 n2 n1 \<Rightarrow>
           (fst(slicebv bvold n2 n1) \<noteq> fst(slicebv bvnew n2 n1)) \<and> (q1 = q2)
       | exp_name q2 \<Rightarrow> q1 = q2
       | _ \<Rightarrow> False)
    | _ \<Rightarrow> False
    )"

(*is listening event triggered? yes, if variable q exists in sense list of event and 
 polarity/value changes. *)
 definition isletrgd:: "env \<Rightarrow> name \<Rightarrow> bitvector \<Rightarrow> bitvector \<Rightarrow> event \<Rightarrow> bool" where
  "isletrgd en q bvold bvnew ev = (case ev of
     evt_listn trgs K \<Rightarrow> filter (letriger en q bvold bvnew) trgs \<noteq> []
   | _ \<Rightarrow> False
   )"

(*trigger listening events. a listening event is triggered if new value is different or polarity
 changes. returns triggered events.*)
 fun trglevents :: "env \<Rightarrow> name \<Rightarrow> bitvector \<Rightarrow> bitvector \<Rightarrow> event list \<Rightarrow> event list" where
  "trglevents en q bvo bvn LE = (case LE of
    Nil \<Rightarrow> []
  | ev#evl \<Rightarrow> if isletrgd en q bvo bvn ev 
             then ev#(trglevents en q bvo bvn evl) else trglevents en q bvo bvn evl)"
 
(************************ Processing listening events *******************************)

(*convert listening event to a process and evaluate lhs for listening events
 registered by cont assignments. (e = e'). evaluate lhs now, and keep its original
 body for later retrieval of the listening event. *)
 definition letoprocbv:: "env \<Rightarrow> event \<Rightarrow> process" where
  "letoprocbv en ev = (case ev of
    evt_listn sl (cpt_dca d el e e') \<Rightarrow> cpt_dca d el e (exp_bv (evalexp en e))
  | evt_listn sl K \<Rightarrow> cpt_alw sl K
  | _ \<Rightarrow> cpt_stm stm_skip
 )"

(*update configuration. when an update occurs, the new binding is added or an existing one in 
 environment is updated. the update in addition may, trigger listening events registered by both
 cont assign or always block or statement. For cont assigns, polarity is not considered. activated
 processes are executed and based on the delays, they are either executed immediately or added to
 future or inactive events. ACTIVATED events are ERASED from listening events.*)
 definition updateconfig :: "name \<Rightarrow> bitvector \<Rightarrow> bitvector \<Rightarrow> configuration \<Rightarrow> configuration" where
  "updateconfig q bvo bvn C = 
     (let (en, LE) = (cfg_env C, cfg_listne C) in
     let TLE = trglevents en q bvo bvn LE in
      let NTLE = listminus LE TLE in

       (C\<lparr>cfg_actp:= (cfg_actp C)@ map (letoprocbv en) TLE,
          cfg_listne:= NTLE
         \<rparr>)
      )"

(*process update events. if old value is different than new one, update occurs, otherwise
  nothing is affected.*)
 fun processue:: "configuration \<Rightarrow> event list \<Rightarrow> configuration" where
  "processue C evl = (case evl of
     [] \<Rightarrow> C 
   | (evt_upd e bvn)#evl' \<Rightarrow> (case nameexp e of
        Some q \<Rightarrow> let bvo = getbvenv q (cfg_env C) in 
          (if bvo \<noteq>  bvn
           then let C' = (C\<lparr>cfg_env:= updatevar (cfg_env C) e bvn\<rparr>) in 
                let C'' = updateconfig q bvo bvn C' in 
                processue C'' evl'
           else C)
      | None \<Rightarrow> C)
   | _ \<Rightarrow> C)"

(*****************************************************************************************)
(************************* Processing blocking/non-blocking assignments *******************)
(*****************************************************************************************)

(*process blocking assignment: normal, zero, non-zero delay, triggered (sensitivity set and 
  trg_star). normal blocking assign statement is executed immediately, which may update env and
  activate listening events, which in turn are added to active processes. other statements are
  added to inactive (zero-delay), future (delay) or listening events (triggered). If there is 
  any computation left in the process, the execution starts with that, followed by new activated
  processes. size of the rhs (evaluated exp) is adjusted according to the lhs variables (or tuple).
  if there is no delay, the list of events (in case of tuple) are executed first followed by the
  rest of computation in process*) 
 definition processba:: "configuration \<Rightarrow> statement \<Rightarrow> configuration" where
  "processba C s = (case s of
    stm_seq (stm_dba el d e) K \<Rightarrow> let bv = (fst(evalexp (cfg_env C) e), (sizeofexp el (cfg_env C) e)) in
      let C' = processue C (mkuevents (cfg_env C) el bv) in
       (if d<0 then (C'\<lparr>cfg_actp:= (cfg_actp C')@[cpt_stm K]\<rparr>) 
         else (if d = 0 then (C \<lparr> cfg_inacte := (cfg_inacte C) @ [evt_inact (cpt_stm (stm_seq (stm_dba el (-1) e) K))]\<rparr>)
         else (C \<lparr>cfg_fute := addevent (evt_fut (nat(d) + cfg_time C) (cpt_stm (stm_seq (stm_dba el (-1) e) K))) (cfg_fute C)\<rparr>))
       )
  | (stm_dba el d e) \<Rightarrow> let bv = (fst(evalexp (cfg_env C) e), (sizeofexp el (cfg_env C) e)) in
        (if d<0 then processue C (mkuevents (cfg_env C) el bv)
           else (if d = 0 then (C \<lparr> cfg_inacte := (cfg_inacte C) @ [evt_inact (cpt_stm (stm_dba el (-1) e))]\<rparr>)
           else (C \<lparr>cfg_fute := addevent (evt_fut (nat(d) + cfg_time C) (cpt_stm (stm_dba el (-1) e))) (cfg_fute C)\<rparr>))
        )
  | stm_seq (stm_tba el sl e) K \<Rightarrow>  let sl' = (if sl = [trg_star] then (senslexp e) else sl) in
        (C \<lparr>cfg_listne := (cfg_listne C)@[evt_listn sl (cpt_stm (stm_seq (stm_dba el (-1) e) K))]\<rparr>)
  | (stm_tba el sl e) \<Rightarrow>  let sl' = (if sl = [trg_star] then (senslexp e) else sl) in
        (C \<lparr>cfg_listne := (cfg_listne C)@[evt_listn sl (cpt_stm (stm_dba el (-1) e) )]\<rparr>)
  | _ \<Rightarrow> C
  )"

(*process non-blocking assignment: normal, zero, non-zero delay, triggered (sensitivity set and
 trg_star). add the statement to nbaue (normal), inactive (zero delay), future (delay), or 
 listening events (triggered). The size of the rhs (evaluated exp) is adjusted according to the
 lhs variables (or tuple). only non recursive cases are dealt with here. the rest of computations
 of a process is allowed to complete before the update event(s) make any changes to environment.*) 
 definition  processnba:: "statement \<Rightarrow> configuration \<Rightarrow> configuration" where
  "processnba s C = (case s of
    stm_dnba el d e \<Rightarrow> let bv = (fst(evalexp (cfg_env C) e), (sizeofexp el (cfg_env C) e)) 
      in (if d < 0 then C\<lparr>cfg_nbaue:= (cfg_nbaue C)@(mkuevents (cfg_env C) el bv)\<rparr> 
         else if d = 0 then (C\<lparr>cfg_inacte := (cfg_inacte C)@[evt_inact (cpt_stm (stm_dnba el (-1) e))]\<rparr>)
         else (C\<lparr>cfg_fute := 
           addevent (evt_fut (nat(d) + cfg_time C) (cpt_stm (stm_dnba el (-1) e))) (cfg_fute C)\<rparr>))
   | stm_tnba el sl e \<Rightarrow> let sl' = (if sl = [trg_star] then (senslexp e) else sl) in
      (C \<lparr>cfg_listne := (cfg_listne C)@[evt_listn sl' (cpt_stm (stm_dnba el (-1) e))]\<rparr>)
   | _ \<Rightarrow> C
  )" 

(*********************************************************************************************)
(************************** Operational Semantics ********************************************)
(*********************************************************************************************)

(************************** Executing processes and events ***********************************)

(*evaluates case statements (get deep into bottom, if nested)*)
 fun evalcase:: "env \<Rightarrow> statement \<Rightarrow> statement" where
  "evalcase en s = (case s of
     stm_case e cl ds \<Rightarrow> (case cl of 
          [] \<Rightarrow> evalcase en ds
        | (c#cl') \<Rightarrow> (if fst(evalexp en e) = fst(evalexp en (fst(c))) 
          then evalcase en (snd(c))
          else (evalcase en (stm_case e cl' ds)) ) )
  | _ \<Rightarrow> s
  )" 

(*takes a statement (at head, if sequence) one step ahead. if statement is nested, it unrolls it
 down (e.g., if true (if true ts f1s) f2s \<rightarrow> f1s)). the body of the named code block is
 skipped if the name is disabled. TODO: while loop is currently executed only once.*)
 fun stepstm :: "configuration \<Rightarrow> statement \<Rightarrow> statement" where
  "stepstm C s = (case s of
    stm_ife e ts fs \<Rightarrow>
      (if fst(evalexp (cfg_env C) e) = 1 then (stepstm C ts) else (stepstm C fs))
  | stm_while e s \<Rightarrow> 
      (if fst(evalexp (cfg_env C) e) = 1
      then (stepstm C s) else stm_skip)
  | stm_cb on s' \<Rightarrow>
      (case on of 
         None \<Rightarrow> (stepstm C s')
       | Some q \<Rightarrow> (if q \<in> (cfg_disabs C) then stm_skip
         else (stepstm C s')) )
  | stm_case ce cl ds \<Rightarrow> evalcase (cfg_env C) s
  | stm_seq s1 s2 \<Rightarrow> stm_seq (stepstm C s1) s2
  | _ \<Rightarrow> s)"  

(*Statement execution (small-step semantics). a statement can update listening, inactive, active,
 and future events. normal blocking assignment is executed first followed by the statement (if 
 there is any). delayed or triggered blocking assignment (and the statement followed if there is
 any) are added to inactive, listening or future events. in non-blocking assignment, the statement
 followed (if there is any) is executed first followed by the non-blocking assignment. *)
 fun execstm :: "statement \<Rightarrow> configuration \<Rightarrow> configuration" where 
    "execstm stm_finish C = (C\<lparr>cfg_finish:= True\<rparr>)"
  | "execstm (stm_disab q) C = (C\<lparr>cfg_disabs:= (cfg_disabs C) \<union> {q}\<rparr>)"

  | "execstm (stm_seq (stm_dba el d e) K) C = processba C (stm_seq (stm_dba el d e) K)"
  | "execstm (stm_seq (stm_tba el sl e) K) C = processba C (stm_seq (stm_tba el sl e) K)"
  | "execstm (stm_dba el d e) C = processba C (stm_dba el d e)"
  | "execstm (stm_tba el sl e) C = processba C (stm_tba el sl e)"

  | "execstm (stm_seq (stm_dnba el d e) K) C = processnba (stm_dnba el d e) (execstm K C)"
  | "execstm (stm_seq (stm_tnba el sl e) K) C = processnba (stm_tnba el sl e) (execstm K C)"
  | "execstm (stm_dnba el d e) C = processnba (stm_dnba el d e) C"
  | "execstm (stm_tnba el sl e) C = processnba (stm_tnba el sl e) C"

  | "execstm (stm_sensl sl s) C = (let sl' = if sl = [trg_star] then (senslstm s) else sl 
       in (C\<lparr>cfg_listne := (evt_listn sl (cpt_stm s))#(cfg_listne C)\<rparr>))"
  | "execstm (stm_seq s1 s2) C = execstm s2 (execstm s1 C)"
  | "execstm _ C = C"

(*execute process and update configuration. New processes (e.g., when listening events activated
 to processes) may be added. [stepstm] takes some statements one step further to make them ready
 for execution. if a process adds any process to active processes, they are executed by recursive
 calls. in each recursive call, the sum of processes in active process and listening events 
 reduces. if a statement process adds to listening events but not to active processes, the termi-
 nation condition (t' < t) will not be satisfied and function will terminate. this is ok, as there
 is no process to execute. After a computation (or process, if it is single computation process) 
 and all newly activated processes are executed, execution starts with new activated processes. 
 When an activated process (listening event registered by always or cont assign) is completely 
 executed (all computations, followed by activated processes) then activated process is added back
 to listening events. See last two cases below *)
 fun execproc :: "nat \<Rightarrow> process \<Rightarrow> configuration \<Rightarrow> configuration"   where 
    "execproc t (cpt_stm s) C  = (let C' = execstm (stepstm C s) C in 
      let t' = (countcptpl
                (cfg_env C') (cfg_actp C')) + (countcptel (cfg_env C') (cfg_listne C')) in
         (case (cfg_actp C', t' < t) of
              (p#pl, True) \<Rightarrow> fold (execproc t') (p#pl) (C'\<lparr>cfg_actp:= []\<rparr>)
             | (_, _) \<Rightarrow> C'))"
  | "execproc t (cpt_alw sl k) C =
      (let C' = execproc t k C in
       (C'\<lparr>cfg_listne:= (cfg_listne C')@[(evt_listn sl k)]\<rparr>))"
  | "execproc t (cpt_dca d el e e') C =
      (let C' = (if d < 0 then execstm (stm_dba el (-1) e') C
                else execstm (stm_delay (nat d) (stm_dba el (-1) e')) C) in 
       let t' = (countcptpl (cfg_env C') (cfg_actp C')) + (countcptel (cfg_env C') (cfg_listne C')) in
         (case (cfg_actp C', t' < t) of
           (p#pl, True) \<Rightarrow> let C'' = fold (execproc t') (p#pl) (C'\<lparr>cfg_actp:= []\<rparr>) in 
               (C''\<lparr>cfg_actp:= [], cfg_listne:= (cfg_listne C'')@[(evt_listn (senslexp e) (cpt_dca d el e e))]\<rparr>)
         | ([], _) \<Rightarrow> (C'\<lparr>cfg_listne:= (cfg_listne C')@[(evt_listn (senslexp e) (cpt_dca d el e e))]\<rparr>)
         | (_, _) \<Rightarrow> C')
      )"

(*execute all processes. for each process, the number of computations in the process and
 all processes in listening events, is used as termination condition in function [execproc].*)
 fun execprocs :: "process list \<Rightarrow> configuration \<Rightarrow> configuration" where 
   "execprocs [] C = C"
 | "execprocs (p#xs) C = 
     (let t = (countcpt (cfg_env C) p) + (countcptel (cfg_env C) (cfg_listne C)) in 
     execprocs xs (execproc t p C))" 

 
(*process a single update event. an update event can trigger listening events to active 
 processes and reduce listening events. [evt_updl] is added by inactive events and when
 all events in the list are executed, execution starts with rest of computation, followed
 by the newly created active processes. [evt_upd] is added by cont assigns with no delay*)
 fun processevent :: "event \<Rightarrow> configuration \<Rightarrow> configuration" where
    "processevent (evt_updl evl K) C = 
          (let C' = processue C evl in (C'\<lparr>cfg_actp:= [K]@(cfg_actp C')\<rparr>) )"
  | "processevent (evt_upd e bv) C = processue C [evt_upd e bv]"
  | "processevent _ C = C"

(*process each update event in the state*)
 fun processevents :: "event list \<Rightarrow> configuration \<Rightarrow> configuration" where
   "processevents evl C =  fold processevent evl (C\<lparr>cfg_upde:= []\<rparr>)"

(*********************************************************************************************)
(*************** Simulate the Verilog program (configuration) ********************************)
(*********************************************************************************************)

(*convert an inactive event to a process*)
 definition activate:: "event \<Rightarrow> process" where
  "activate e = (case e of 
    evt_inact K \<Rightarrow> K
  | _ \<Rightarrow> cpt_stm stm_skip)"

(*a future event is awaken if current time match its time*)
 definition awake:: "nat \<Rightarrow> event \<Rightarrow> bool" where
 "awake n1 e = (case e of 
    evt_fut n2 K \<Rightarrow> n1 = n2
  | _ \<Rightarrow> False)"

(*convert future event to process*)
 definition futtoproc :: "event \<Rightarrow> process" where
   "futtoproc e = (case e of 
     evt_fut n k \<Rightarrow> k
   | _ \<Rightarrow> cpt_stm stm_skip)"

(*cancel continuous future event. a cont future event is cancelled if it is also
 scheduled at a later time. currently, only net name are supported and bit slice, select, 
 index are not considered. The list of events is assumed to be sorted by time*)
 fun cancel :: "event \<Rightarrow> event list \<Rightarrow> bool" where
  "cancel ev evl = (case evl of 
     [] \<Rightarrow> False
   | (ev'#evl') \<Rightarrow> (case (ev, ev') of
      (evt_fut _ (cpt_dca _ [exp_name q1] _ _), 
        evt_fut _ (cpt_dca _ [exp_name q2] _  _)) \<Rightarrow> 
         (if q1 = q2 then True else cancel ev evl')
      | (_,_) \<Rightarrow> cancel ev evl')
  )"

(*cancelling (as explained by Gordon). future events list [evl] must be sorted by time. 
 for simplicity, cancelling is currently supported by net variables only (bitslice, index
 are not considered)*)
 fun cancelling :: "event list \<Rightarrow> event list" where
  "cancelling evl = (case evl of
    [] \<Rightarrow> []
  | (e#evl') \<Rightarrow> (if cancel e evl' then cancelling evl' else e#cancelling evl'))"

(*converts Verilog module (program) to configuration*)
 definition state:: "program \<Rightarrow> configuration" where
  "state P = (case P of 
      (prog_mod nms tpl) \<Rightarrow>  mkconfig tpl)"

(*prepare the configuration for next cycle and advance time to the time of future
 event at head (of sorted list).*)
 definition newcycle :: "configuration \<Rightarrow> configuration" where
  "newcycle C =  
     (let FE = cancelling (cfg_fute C) in 
      let nt = timeofhd(FE) in
      let FE' = filter (awake nt) FE in
       (C\<lparr>cfg_actp:= map futtoproc FE',
          cfg_fute:= listminus FE FE',
          cfg_time:= nt\<rparr>)
      )" 

(*simulation moves to next cycle if active processes of any kind are exhausted and
 there are still future events to execute and program has not yet terminated.*)
 definition nextcycleb :: "configuration \<Rightarrow> bool" where
   "nextcycleb C = (
     cfg_upde C = [] \<and> cfg_actp C = [] \<and> cfg_inacte C = [] \<and> cfg_nbaue C = [] \<and>
     (cfg_fute C \<noteq> [] \<and> (Not(cfg_finish C)) ))"

(*if there exists processes of any type, process them (return True) *)
 definition nextpassb :: "configuration \<Rightarrow> bool" where
   "nextpassb C = (
     (cfg_upde C \<noteq> [] \<or> cfg_actp C \<noteq> [] \<or> cfg_inacte C \<noteq> [] \<or> cfg_nbaue C \<noteq> []) 
     \<and> (Not(cfg_finish C)) )"
   

(*step simulation. exhausts all processes of any type in the current simulation cycle.
 update events may create active processes and active process may create other processes.
 event processing must be followed by process execution as the former trigger/activate listening
 events to processes. In a single pass, initially events are processed followed by initial active
 processes. Then all inactive events are activated and processed, which is followed by [nbaue]
 events created so far, followed by processes created by these later events. After this single
 pass, the state may have future, inactive and nbaue events created during this single pass.*) 
 definition stepsim:: "configuration \<Rightarrow> configuration" where
  "stepsim C =
    (let Cap = processevents (cfg_upde C) (C\<lparr>cfg_upde:= []\<rparr>) in
    (let Cie = execprocs (cfg_actp Cap) (Cap\<lparr>cfg_actp:= []\<rparr>) in
    (let PL = (map activate (cfg_inacte Cie)) in
    (let Cnba = execprocs PL (Cie\<lparr>cfg_actp:=[], cfg_inacte:= []\<rparr>) in
    (let Cfinal = processevents ([evt_updl (cfg_nbaue Cnba) (cpt_stm stm_skip)])
                            (Cnba\<lparr>cfg_upde:= [], cfg_nbaue:= []\<rparr>) in
     execprocs (cfg_actp Cfinal) (Cfinal\<lparr>cfg_actp:= []\<rparr>) )) ) ) )
  " 
 
(*simulate a state m number of times. a state is executed at least once (m = 0). If there
 are any future, or inactive/nbaue events, they are executed until the simulation cycle 
 reduces to 0.*)
 fun simulate :: "nat \<Rightarrow> configuration \<Rightarrow> configuration" where
   "simulate m C =  (case (m > 0, nextcycleb C, nextpassb C) of
         (True, True, _) \<Rightarrow> simulate (m-1) (stepsim (newcycle C))
       | (True, False, True) \<Rightarrow> simulate (m-1) (stepsim C)
       | (False, _, True) \<Rightarrow> stepsim C
       | (_, _, _) \<Rightarrow> C)"   


(*for testing only*)
definition fedinput':: "configuration \<Rightarrow> configuration" where
 "fedinput' C = (let C' = (initconfig\<lparr>cfg_actp:= (cfg_actp C)\<rparr>) in 
               simulate 0 C')"
           


value "simulate 2 
   \<lparr>cfg_env =
    [(X, 0, 4), (Y, 0, 4),
     (Z, 0, 4)],
    cfg_time = 0,
    cfg_actp =
      [cpt_stm
        [#] 1 BEGIN : [None] IF \<^sub>l\<^sub>nY [==] \<^sub>v(0, 4)
                  THEN ([\<^sub>nZ] [=] [#] - 1 \<^sub>v(6, 4))
                  ELSE (([\<^sub>nZ] [=] [#] - 1 \<^sub>v(7, 4));;
                       ([\<^sub>nX] [=] [#] - 1 \<^sub>v(1, 4));;
                       ([\<^sub>nX] [=] [#] - 1 \<^sub>v(1, 4));;
                       $finish)
             END],
    cfg_upde = [evt_upd (\<^sub>nY) (5, 4)], cfg_inacte = [], cfg_nbaue = [],
    cfg_fute = [], cfg_listne = [], cfg_disabs = {}, cfg_finish = False\<rparr>"


(* ;;
                           (([\<^sub>nX] [=] [#] - 1 \<^sub>v(1, 4)) ;;
                           ([\<^sub>nX] [=] [#] - 1 \<^sub>v(1, 4))) ;;
                  $finish*)

(*
 fun simulate :: "nat \<Rightarrow> nat \<Rightarrow> configuration \<Rightarrow> configuration" where
   "simulate m n C =
     (let C' = (if nextcycleb C then newcycle C else C) in
      if (cfg_time (newcycle C)) \<le> m \<and> n > 0 then simulate m (n-1) (stepsim C')
      else (stepsim C'))"  
*)

(*TODO: executing non-blocking assign update and inactive events added by (activated 
 (inactive and nbaue)) processes. recursive, termination?. nbaue is just update event, 
 which can only activate listening events, which are executed recursively using 
 [expecprocesses]. The other case is tricky when delayed statements are nested such as 
 ([#] 0 ([#] 0 stm), which should be avoided in programs.*) 

(*Non-terminating loop with delays: a scenario could be of loop (initial-cont assign-always) with
 zero dealy cont assignment, such as 
 
    assign #0 x = y
    initial y = 2
    always @(x) y = y + 1

 In this case, listening events are initially registered and when the rhs changes (by initial), it 
 is triggered, adding event to inactive event, and adding the same listening event
 back to listening events, completing one [execprocs] execution. when that awaked inactive 
 event is executed, by next [execprocs], it activates the always listening event, which again
 trigers cont assign listening event, and repeats. This would lead to non termination, 
 but the above sequence would stop it, by executing [execprocs] only three times.
 All other non-terminating programs are terminated normally by [execproc] by removing the
 listening event until the active process of the same listening is completely executed. *)

(*simulate the program until max (m) cycle. the difference (d) decreases in each recursive call.
 initially it is equal to maximum (max - (cycle 0) = max). the time control [d] is added for 
 termination. the function can not be made recursive, as future events can add other future events.
 First [nat] is the maximum number of simulation cycle, and the difference (m - d) always 
 decreases, causes termination. *)
(*  fun simulate :: "nat \<Rightarrow> nat \<Rightarrow> configuration \<Rightarrow> configuration" where
   "simulate m d C' = 
     (let C = (if (cfg_time C') = 0 then stepsim C' else C') in 
     (let d' = m - cfg_time (newcycle C) in
      (if nextcycleb C \<and> d' < d \<and> (cfg_time (newcycle C)) \<le> m
      then simulate m d' (stepsim (newcycle C))
      else C)
     ))"   *)

end