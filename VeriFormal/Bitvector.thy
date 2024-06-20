theory Bitvector
 imports Main "~~/src/HOL/Word/Word"
begin
 
(*the value and size of bitvector*)
 type_synonym bitvector = "(int * nat)"

  (*shifts vector v1 right by n, with the result of size l*)
 definition bvrsn:: "bitvector \<Rightarrow> nat \<Rightarrow> bitvector" where
   "bvrsn v1 n = (fst(v1) >> n, snd(v1))"

 definition bvlsn:: "bitvector \<Rightarrow> nat \<Rightarrow> bitvector" where
   "bvlsn v1 n = (fst(v1) << n,  snd(v1))" 

(*mask of n bits (*n number of 1's*)*)
 definition maskn:: "nat \<Rightarrow> int" where
  "maskn n = (2^n) - 1"
 
(*gets slice (bits n1 till n2, where n2 \<ge> n1) of a bitvector bv. slice bv n n, returns
 bit at nth position. *)
 definition slicebv:: "bitvector \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bitvector" where
  "slicebv bv n2 n1 = (bitAND (shiftr (fst bv) n1) (maskn((n2-n1)+1)), (n2-n1)+1)"

(*Replaces bits n1 to n2 (with n2 \<ge> n1) in bv1 with bits in bv2.*)
  definition slicebva :: "bitvector \<Rightarrow> bitvector \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> bitvector" where
  "slicebva bv1 bv2 n2 n1 = 
   (((fst bv1) AND (NOT (maskn((n2-n1)+1) << n1))) OR (((fst bv2) AND maskn((n2-n1)+1)) << n1), snd(bv1))" 
 
(* Both are the same in functionality. Note the difference... isn't it amazing? 

 definition slicebva:: "bitvector \<Rightarrow> bitvector \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> bitvector" where
  "slicebva bv1 bv2 n2 n1 = 
   ((fst(bv1) AND (NOT (maskn((n2-n1)+1) << n1))) OR ((fst(bv2) << n1) AND (maskn((n2-n1)+1) << n1)), snd(bv1))" 
 *)

(*bitvectors concatenation. bv1 is shifted left by n and then first n bits of bv1 are 
  replaced with bv2 (with n is the size of bv2). 
 NOTE: the resultant value may be greater than the length of vector, but would be later truncated
  when stored in a variable (e.g., concbv (4, 2) (0, 3)) = (32, 5) *)
 definition concbv :: "bitvector \<Rightarrow> bitvector \<Rightarrow> bitvector" where
  "concbv bv1 bv2 =   (let bv = bvlsn (fst bv1, (snd bv1) + (snd bv2)) (snd bv2) in
    slicebva bv bv2 ((snd bv2)-1) 0)"


(*Unary bitvector operations*)
 datatype uop =
   bvPOS  ("[++]")
 | bvNEG  ("[--]")
 | bvNOT  ("[!]")   
 | bvCOMP ("[~]") (*+, -, !, ~ *) 
  (*| bvAND | bvNAND | bvOR | bvNOR | bvXOR | bvXNOR *)  (*gates:  &, ~&, |, ~|, ^, ~^^~ *) 
 
(*Binary bitvector operations*) 
 datatype bop = 
   bvsMULT  ("[*]")
 | bvsPLUS  ("[+]")
 | bvsSUB   ("[-]")
 | bvsDIV   ("[/]")
 | bvsMOD   ("[%]")            (**, +, -, /, % (arithemetic)*)
 | bvsAND   ("[&]")  
 | bvsOR    ("[|]")
 | bvsXOR   ("[^]")
 | bvsXNOR  ("[~^]")           (*&, |, ^, ~^^~*) 
 | bvsCONC  ("[+++]")          (* concatenation {}*)

(*Boolean (logical) bitvector operations *)
 datatype lop =  (*<, <=, >, >=, ==, !=, &&, ||*) 
   bvsLT    ("[<]")
 | bvsLTE   ("[<=]")
 | bvsGT    ("[>]")
 | bvsGTE   ("[=>]")
 | bvsEQ    ("[==]")
 | bvsNEQ   ("[!=]")
 | bvsLAND  ("[&&]")      
 | bvsLOR   ("[||]")

 definition unopbv:: "uop \<Rightarrow> bitvector \<Rightarrow> bitvector" where
  "unopbv vop v \<equiv> (case vop of 
    bvPOS \<Rightarrow> (if fst(v) < 0 then (-fst(v), snd(v)) else v)  (*todo: puting + or reversing -?*)
  | bvNEG \<Rightarrow> (-fst(v), snd(v)) 
  | bvNOT \<Rightarrow> (if fst(v) \<ge> 1 then (0, snd(v)) else (1, snd(v)))  (*turns nonzero/true value of the operand into 0, zero or false value into 1*)
  | bvCOMP \<Rightarrow> (NOT(fst(v)), snd(v))  (*inverts all the bits*)
  (*| other unary operations*) 
  )"

 (*Binary bitvectors operations*)
 definition binopbv :: "bitvector \<Rightarrow> bop \<Rightarrow> bitvector \<Rightarrow> bitvector" where
  "binopbv v1 vop v2 \<equiv> (case vop of 
    bvsAND \<Rightarrow> (fst(v1) AND fst(v2), max (snd(v1)) (snd(v2))) 
  | bvsOR \<Rightarrow> (fst(v1) OR fst(v2), max (snd(v1)) (snd(v2)))
  | bvsXOR \<Rightarrow> (fst(v1) XOR fst(v2), max (snd(v1)) (snd(v2)))
  | bvsXNOR \<Rightarrow> (NOT(fst(v1) XOR fst(v2)), max (snd(v1)) (snd(v2)))     (* value 'nat(NOT(2 XOR 1))' *)
  | bvsMULT \<Rightarrow> (fst(v1) * fst(v2), (snd(v1)) + (snd(v2)))      (*(snd(v1)) + (snd(v2)),  all of the rest: max (snd(v1)) (snd(v2))*)
  | bvsPLUS \<Rightarrow> (fst(v1) + fst(v2), max (snd(v1)) (snd(v2)))
  | bvsSUB \<Rightarrow> (fst(v1) - fst(v2), max (snd(v1)) (snd(v2)))
  | bvsDIV \<Rightarrow> (fst(v1) div fst(v2), max (snd(v1)) (snd(v2)))
  | bvsMOD \<Rightarrow> (fst(v1) mod fst(v2), max (snd(v1)) (snd(v2))) 
  | bvsCONC \<Rightarrow> concbv v1 v2
  (* | other binary operations *)
 )"

 definition booltobv :: "bool \<Rightarrow> bitvector" where
  "booltobv b \<equiv> (if b then (1, 1) else (0, 1))"

 definition lopbv :: "bitvector \<Rightarrow> lop \<Rightarrow> bitvector \<Rightarrow> bitvector" where
  "lopbv v1 vop v2 \<equiv> (case vop of 
    bvsLT \<Rightarrow> booltobv(fst(v1) < fst(v2))
  | bvsLTE \<Rightarrow> booltobv(fst(v1) \<le> fst(v2))
  | bvsGT \<Rightarrow> booltobv(fst(v1) > fst(v2))
  | bvsGTE \<Rightarrow> booltobv(fst(v1) \<ge> fst(v2))
  | bvsEQ \<Rightarrow> booltobv(fst(v1) = fst(v2))
  | bvsNEQ \<Rightarrow> booltobv(fst(v1) \<noteq> fst(v2))
  | bvsLAND \<Rightarrow> booltobv((fst(v1) \<ge> 1) \<and> (fst(v2) \<ge> 1))
  | bvsLOR \<Rightarrow> booltobv((fst(v1) \<ge> 1) \<and> (fst(v2) \<ge> 1))
  )"

value "nat(max 2 0)"


 end