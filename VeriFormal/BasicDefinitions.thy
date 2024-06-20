theory BasicDefinitions
 imports Syntax "~~/src/HOL/Finite_Set" Orderings
begin


(****************************** Axillarry functions ****************************************)

(*retrieves value of identifier [name] from environment [env] *)
 fun getbvenv:: "name \<Rightarrow> env \<Rightarrow> bitvector" where
 "getbvenv q en = (case en of
    [] \<Rightarrow> (0,0) 
  | (p#pl) \<Rightarrow> (if fst(p) = q then snd(p) else (getbvenv q pl)))"

(*time of future event*)
 definition timeof :: "event \<Rightarrow> nat" where
  "timeof ev \<equiv> (case ev of 
    evt_fut n _ \<Rightarrow> n
  | _ \<Rightarrow> 0)"

 definition timeofhd :: "event list \<Rightarrow> nat" where
  "timeofhd evl = (case evl of
    Nil \<Rightarrow> 0
  | ev#evl' \<Rightarrow>  timeof ev
  )"

(*is event less than or equal to every event in the list by time.*)
 primrec eventleq :: "event \<Rightarrow> event list \<Rightarrow> bool" where
   "eventleq ev [] = True"
 | "eventleq ev (x#xs) = (timeof(ev) \<le> timeof(x) \<and> eventleq ev xs)"

(*is event list sorted by time*)
 primrec evtsorted :: "event list \<Rightarrow> bool" where
   "evtsorted [] = True"
 | "evtsorted (x#xs) = (eventleq x xs \<and> evtsorted xs)"

(*insert event in the list, preserving order, low(head)-higher*)
 primrec addevent :: "event \<Rightarrow> event list \<Rightarrow> event list" where
   "addevent ev [] = [ev]"
 | "addevent ev (x#xs) = (if timeof(ev) \<le> timeof(x) then ev#x#xs else x # addevent ev xs)"
 
(*sort future events by time - event with lowest time first*)
 primrec sortevents :: "event list \<Rightarrow> event list" where
   "sortevents [] = []"
 | "sortevents (x#xs) = addevent x (sortevents xs)"

(*get sensitivity list from expression. all variable expression (e.g., x[2], x) in the expression.
 A change to any of these variables or a particular bit(s) on rhs of continuous assign or 
 procedural assignment (in case of \<star>) will trigger a (cont) listening event. *)
 fun senslexp:: "exp \<Rightarrow> sensl" where
  "senslexp e = (case e of 
     exp_name q \<Rightarrow> [trg_exp e]
   | exp_bv _ \<Rightarrow> []
   | exp_uop _ e' \<Rightarrow> senslexp e'
   | exp_bop e1 _ e2 \<Rightarrow> senslexp e1 @ senslexp e2
   | exp_lop e1 _ e2 \<Rightarrow> senslexp e1 @ senslexp e2
   | exp_cop e te fe \<Rightarrow> senslexp e @ senslexp te @ senslexp fe
   | exp_rsn e' _ \<Rightarrow> senslexp e'
   | exp_lsn e' _ \<Rightarrow> senslexp e'
   | exp_bitslice q _ _ \<Rightarrow> [trg_exp e]
   | exp_bitsel q _ \<Rightarrow> [trg_exp e]
   | exp_index q _ \<Rightarrow> [trg_exp e]
  )" 

(*get sensitivity list from the triggered statement (in case of (\<star>)).
 The list should include all signals that appear on the rhs of any assignment.
 TODO: nested trigger statements allowed (the case of [stm_sensl])?*) 
 fun senslstm :: "statement \<Rightarrow> sensl"where
  "senslstm s = (case s of 
     stm_seq s1 s2 \<Rightarrow> senslstm s1 @ senslstm s2
   | stm_dba _ _ e \<Rightarrow> senslexp e
   | stm_tba _ _ e \<Rightarrow> senslexp e
   | stm_dnba _ _ e \<Rightarrow> senslexp e
   | stm_tnba _ _ e \<Rightarrow> senslexp e
   | stm_ife e ts fs \<Rightarrow> senslstm ts @ senslstm fs   (*really so?*)
   | stm_while e s \<Rightarrow> senslstm s                    (*how many times?*)
   | stm_cb _ s \<Rightarrow>senslstm s
   | stm_case e csl ds \<Rightarrow> (case csl of 
       Nil \<Rightarrow> senslstm ds 
     | cs#csl' \<Rightarrow> senslstm (snd cs) @ senslstm (stm_case e csl' ds))
   | stm_sensl _ s \<Rightarrow> senslstm s
   | stm_delay _ s \<Rightarrow> senslstm s
   | _ \<Rightarrow> []
 )"

(*get variable name of the expression*)
 fun nameexp :: "exp \<Rightarrow> name option" where
   "nameexp (exp_name q) = Some q"
 | "nameexp (exp_bitslice q n2 n1) = Some q"
 | "nameexp (exp_bitsel q n) = Some q"
 | "nameexp (exp_index q e') = Some q"
 | "nameexp _ = None"

 (*removes element from list (ONCE). If duplicate copies of [a] exists in list, 
  only one is removed. *)
 fun remove:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "remove x [] = []" 
  | "remove x (y#ys) = (if x=y then ys else y# (remove x ys))"

 (*remove all elements of list b from list a (listA - listB)*)
 fun listminus :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "listminus la [] = la"
 | "listminus la (y#ys) = listminus (remove y la) ys"

 
 (*initialize arguments (input ports). every port name is initialized to the integer value,
  by registering a blocking-assign process. it could be an update event instead, but currently
  all events are executed together and the effect of later updates in the list is lost (activated
  listening events by prior update events are restored back after ALL update events are 
  processed.*)
 fun initargs :: "env \<Rightarrow> (name*int) list \<Rightarrow> process list" where 
   "initargs en Nil = Nil"
 | "initargs en (a#argl) = (let s = snd(getbvenv (fst a) en) in 
     [cpt_stm (stm_dba [exp_name (fst a)] (-1) (exp_bv (snd a, s)))]@initargs en argl)"

(*initialize input arguments. a process is created for each initialization and all processes
 created are executed before the program body execution begins. *)
 fun fedinput :: "(name*int) list \<Rightarrow> configuration \<Rightarrow> configuration" where
  "fedinput argl C = (C\<lparr>cfg_actp:= initargs (cfg_env C) argl@(cfg_actp C)\<rparr>)"

end