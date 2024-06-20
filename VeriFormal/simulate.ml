module Evaluate : sig
  type num
  type int
  type nat
  type name
  type program
  type 'a configuration_ext
  val evaluate : int
end = struct

type num = One | Bit0 of num | Bit1 of num;;

let rec equal_num
  x0 x1 = match x0, x1 with Bit0 x2, Bit1 x3 -> false
    | Bit1 x3, Bit0 x2 -> false
    | One, Bit1 x3 -> false
    | Bit1 x3, One -> false
    | One, Bit0 x2 -> false
    | Bit0 x2, One -> false
    | Bit1 x3, Bit1 y3 -> equal_num x3 y3
    | Bit0 x2, Bit0 y2 -> equal_num x2 y2
    | One, One -> true;;

type int = Zero_int | Pos of num | Neg of num;;

let rec equal_inta
  x0 x1 = match x0, x1 with Neg k, Neg l -> equal_num k l
    | Neg k, Pos l -> false
    | Neg k, Zero_int -> false
    | Pos k, Neg l -> false
    | Pos k, Pos l -> equal_num k l
    | Pos k, Zero_int -> false
    | Zero_int, Neg l -> false
    | Zero_int, Pos l -> false
    | Zero_int, Zero_int -> true;;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_int = ({equal = equal_inta} : int equal);;

let rec plus_num
  x0 x1 = match x0, x1 with Bit1 m, Bit1 n -> Bit0 (plus_num (plus_num m n) One)
    | Bit1 m, Bit0 n -> Bit1 (plus_num m n)
    | Bit1 m, One -> Bit0 (plus_num m One)
    | Bit0 m, Bit1 n -> Bit1 (plus_num m n)
    | Bit0 m, Bit0 n -> Bit0 (plus_num m n)
    | Bit0 m, One -> Bit1 m
    | One, Bit1 n -> Bit0 (plus_num n One)
    | One, Bit0 n -> Bit1 n
    | One, One -> Bit0 One;;

let rec times_num
  m n = match m, n with
    Bit1 m, Bit1 n -> Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
    | Bit1 m, Bit0 n -> Bit0 (times_num (Bit1 m) n)
    | Bit0 m, Bit1 n -> Bit0 (times_num m (Bit1 n))
    | Bit0 m, Bit0 n -> Bit0 (Bit0 (times_num m n))
    | One, n -> n
    | m, One -> m;;

let rec times_inta
  k l = match k, l with Neg m, Neg n -> Pos (times_num m n)
    | Neg m, Pos n -> Neg (times_num m n)
    | Pos m, Neg n -> Neg (times_num m n)
    | Pos m, Pos n -> Pos (times_num m n)
    | Zero_int, l -> Zero_int
    | k, Zero_int -> Zero_int;;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a dvd = {times_dvd : 'a times};;

let times_int = ({times = times_inta} : int times);;

let dvd_int = ({times_dvd = times_int} : int dvd);;

let one_inta : int = Pos One;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : int one);;

let rec snd (x1, x2) = x2;;

let rec uminus_int
  = function Neg m -> Pos m
    | Pos m -> Neg m
    | Zero_int -> Zero_int;;

let rec bitM
  = function One -> One
    | Bit0 n -> Bit1 (bitM n)
    | Bit1 n -> Bit1 (Bit0 n);;

let rec dup
  = function Neg n -> Neg (Bit0 n)
    | Pos n -> Pos (Bit0 n)
    | Zero_int -> Zero_int;;

let rec minus_inta
  k l = match k, l with Neg m, Neg n -> sub n m
    | Neg m, Pos n -> Neg (plus_num m n)
    | Pos m, Neg n -> Pos (plus_num m n)
    | Pos m, Pos n -> sub m n
    | Zero_int, l -> uminus_int l
    | k, Zero_int -> k
and sub
  x0 x1 = match x0, x1 with
    Bit0 m, Bit1 n -> minus_inta (dup (sub m n)) (Pos One)
    | Bit1 m, Bit0 n -> plus_inta (dup (sub m n)) (Pos One)
    | Bit1 m, Bit1 n -> dup (sub m n)
    | Bit0 m, Bit0 n -> dup (sub m n)
    | One, Bit1 n -> Neg (Bit0 n)
    | One, Bit0 n -> Neg (bitM n)
    | Bit1 m, One -> Pos (Bit0 m)
    | Bit0 m, One -> Pos (bitM m)
    | One, One -> Zero_int
and plus_inta
  k l = match k, l with Neg m, Neg n -> Neg (plus_num m n)
    | Neg m, Pos n -> sub n m
    | Pos m, Neg n -> sub m n
    | Pos m, Pos n -> Pos (plus_num m n)
    | Zero_int, l -> l
    | k, Zero_int -> k;;

let rec less_num
  m x1 = match m, x1 with Bit1 m, Bit0 n -> less_num m n
    | Bit1 m, Bit1 n -> less_num m n
    | Bit0 m, Bit1 n -> less_eq_num m n
    | Bit0 m, Bit0 n -> less_num m n
    | One, Bit1 n -> true
    | One, Bit0 n -> true
    | m, One -> false
and less_eq_num
  x0 n = match x0, n with Bit1 m, Bit0 n -> less_num m n
    | Bit1 m, Bit1 n -> less_eq_num m n
    | Bit0 m, Bit1 n -> less_eq_num m n
    | Bit0 m, Bit0 n -> less_eq_num m n
    | Bit1 m, One -> false
    | Bit0 m, One -> false
    | One, n -> true;;

let rec less_int
  x0 x1 = match x0, x1 with Neg k, Neg l -> less_num l k
    | Neg k, Pos l -> true
    | Neg k, Zero_int -> true
    | Pos k, Neg l -> false
    | Pos k, Pos l -> less_num k l
    | Pos k, Zero_int -> false
    | Zero_int, Neg l -> false
    | Zero_int, Pos l -> true
    | Zero_int, Zero_int -> false;;

let rec sgn_int
  i = (if equal_inta i Zero_int then Zero_int
        else (if less_int Zero_int i then Pos One else Neg One));;

let rec abs_int i = (if less_int i Zero_int then uminus_int i else i);;

let rec apsnd f (x, y) = (x, f y);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

let rec numeral _A
  = function
    Bit1 n ->
      let m = numeral _A n in
      plus _A.semigroup_add_numeral.plus_semigroup_add
        (plus _A.semigroup_add_numeral.plus_semigroup_add m m)
        (one _A.one_numeral)
    | Bit0 n ->
        let m = numeral _A n in
        plus _A.semigroup_add_numeral.plus_semigroup_add m m
    | One -> one _A.one_numeral;;

type 'a minus = {minus : 'a -> 'a -> 'a};;
let minus _A = _A.minus;;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
    minus_cancel_ab_semigroup_add : 'a minus};;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add;
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};;

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add;
    semiring_0_semiring_0_cancel : 'a semiring_0};;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult;
    semiring_comm_semiring : 'a semiring};;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring;
    semiring_0_comm_semiring_0 : 'a semiring_0};;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0;
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};;

type 'a power = {one_power : 'a one; times_power : 'a times};;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel;
    semiring_1_semiring_1_cancel : 'a semiring_1};;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult;
    monoid_mult_comm_monoid_mult : 'a monoid_mult;
    dvd_comm_monoid_mult : 'a dvd};;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult;
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0;
    semiring_1_comm_semiring_1 : 'a semiring_1};;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel;
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1;
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};;

type 'a comm_semiring_1_diff_distrib =
  {comm_semiring_1_cancel_comm_semiring_1_diff_distrib :
     'a comm_semiring_1_cancel};;

type 'a semiring_parity =
  {comm_semiring_1_diff_distrib_semiring_parity :
     'a comm_semiring_1_diff_distrib};;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};;

type 'a semidom =
  {comm_semiring_1_diff_distrib_semidom : 'a comm_semiring_1_diff_distrib;
    semiring_no_zero_divisors_semidom : 'a semiring_no_zero_divisors};;

type 'a div = {dvd_div : 'a dvd; div : 'a -> 'a -> 'a; moda : 'a -> 'a -> 'a};;
let div _A = _A.div;;
let moda _A = _A.moda;;

type 'a semiring_div =
  {div_semiring_div : 'a div; semidom_semiring_div : 'a semidom};;

type 'a semiring_div_parity =
  {semiring_div_semiring_div_parity : 'a semiring_div;
    semiring_parity_semiring_div_parity : 'a semiring_parity};;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add;
    order_ordered_ab_semigroup_add : 'a order};;

type 'a ordered_semiring =
  {comm_monoid_add_ordered_semiring : 'a comm_monoid_add;
    ordered_ab_semigroup_add_ordered_semiring : 'a ordered_ab_semigroup_add;
    semiring_ordered_semiring : 'a semiring};;

type 'a ordered_cancel_semiring =
  {ordered_semiring_ordered_cancel_semiring : 'a ordered_semiring;
    semiring_0_cancel_ordered_cancel_semiring : 'a semiring_0_cancel};;

type 'a ordered_comm_semiring =
  {comm_semiring_0_ordered_comm_semiring : 'a comm_semiring_0;
    ordered_semiring_ordered_comm_semiring : 'a ordered_semiring};;

type 'a ordered_cancel_comm_semiring =
  {comm_semiring_0_cancel_ordered_cancel_comm_semiring :
     'a comm_semiring_0_cancel;
    ordered_cancel_semiring_ordered_cancel_comm_semiring :
      'a ordered_cancel_semiring;
    ordered_comm_semiring_ordered_cancel_comm_semiring :
      'a ordered_comm_semiring};;

type 'a ordered_cancel_ab_semigroup_add =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
     'a cancel_ab_semigroup_add;
    ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
      'a ordered_ab_semigroup_add};;

type 'a ordered_ab_semigroup_add_imp_le =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
     'a ordered_cancel_ab_semigroup_add};;

type 'a linorder = {order_linorder : 'a order};;

type 'a linordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add;
    linorder_linordered_ab_semigroup_add : 'a linorder};;

type 'a linordered_cancel_ab_semigroup_add =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
     'a linordered_ab_semigroup_add;
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
      'a ordered_ab_semigroup_add_imp_le};;

type 'a ordered_comm_monoid_add =
  {comm_monoid_add_ordered_comm_monoid_add : 'a comm_monoid_add;
    ordered_cancel_ab_semigroup_add_ordered_comm_monoid_add :
      'a ordered_cancel_ab_semigroup_add};;

type 'a linordered_semiring =
  {linordered_cancel_ab_semigroup_add_linordered_semiring :
     'a linordered_cancel_ab_semigroup_add;
    ordered_comm_monoid_add_linordered_semiring : 'a ordered_comm_monoid_add;
    ordered_cancel_semiring_linordered_semiring : 'a ordered_cancel_semiring};;

type 'a linordered_semiring_strict =
  {linordered_semiring_linordered_semiring_strict : 'a linordered_semiring};;

type 'a linordered_comm_semiring_strict =
  {linordered_semiring_strict_linordered_comm_semiring_strict :
     'a linordered_semiring_strict;
    ordered_cancel_comm_semiring_linordered_comm_semiring_strict :
      'a ordered_cancel_comm_semiring};;

type 'a semiring_char_0 = {semiring_1_semiring_char_0 : 'a semiring_1};;

type 'a linordered_semidom =
  {semiring_char_0_linordered_semidom : 'a semiring_char_0;
    linordered_comm_semiring_strict_linordered_semidom :
      'a linordered_comm_semiring_strict;
    semidom_linordered_semidom : 'a semidom};;

type 'a semiring_numeral_div =
  {semiring_div_parity_semiring_numeral_div : 'a semiring_div_parity;
    linordered_semidom_semiring_numeral_div : 'a linordered_semidom};;

let rec divmod_step _A
  l (q, r) =
    (if less_eq
          _A.linordered_semidom_semiring_numeral_div.linordered_comm_semiring_strict_linordered_semidom.linordered_semiring_strict_linordered_comm_semiring_strict.linordered_semiring_linordered_semiring_strict.linordered_cancel_ab_semigroup_add_linordered_semiring.linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add.linorder_linordered_ab_semigroup_add.order_linorder.preorder_order.ord_preorder
          (numeral
            _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_numeral_semiring_1.numeral_semiring_numeral
            l)
          r
      then (plus _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_numeral_semiring_1.numeral_semiring_numeral.semigroup_add_numeral.plus_semigroup_add
              (times
                _A.semiring_div_parity_semiring_numeral_div.semiring_div_semiring_div_parity.div_semiring_div.dvd_div.times_dvd
                (numeral
                  _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_numeral_semiring_1.numeral_semiring_numeral
                  (Bit0 One))
                q)
              (one _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral),
             minus _A.semiring_div_parity_semiring_numeral_div.semiring_div_semiring_div_parity.semidom_semiring_div.comm_semiring_1_diff_distrib_semidom.comm_semiring_1_cancel_comm_semiring_1_diff_distrib.semiring_1_cancel_comm_semiring_1_cancel.semiring_0_cancel_semiring_1_cancel.cancel_comm_monoid_add_semiring_0_cancel.cancel_ab_semigroup_add_cancel_comm_monoid_add.minus_cancel_ab_semigroup_add
               r (numeral
                   _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_numeral_semiring_1.numeral_semiring_numeral
                   l))
      else (times _A.semiring_div_parity_semiring_numeral_div.semiring_div_semiring_div_parity.div_semiring_div.dvd_div.times_dvd
              (numeral
                _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_numeral_semiring_1.numeral_semiring_numeral
                (Bit0 One))
              q,
             r));;

let rec divmod _A
  m n = match m, n with
    Bit1 m, Bit0 n ->
      let (q, r) = divmod _A m n in
      (q, plus _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_numeral_semiring_1.numeral_semiring_numeral.semigroup_add_numeral.plus_semigroup_add
            (times
              _A.semiring_div_parity_semiring_numeral_div.semiring_div_semiring_div_parity.div_semiring_div.dvd_div.times_dvd
              (numeral
                _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_numeral_semiring_1.numeral_semiring_numeral
                (Bit0 One))
              r)
            (one _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral))
    | Bit0 m, Bit0 n ->
        let (q, r) = divmod _A m n in
        (q, times _A.semiring_div_parity_semiring_numeral_div.semiring_div_semiring_div_parity.div_semiring_div.dvd_div.times_dvd
              (numeral
                _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_numeral_semiring_1.numeral_semiring_numeral
                (Bit0 One))
              r)
    | m, n ->
        (if less_num m n
          then (zero _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero,
                 numeral
                   _A.linordered_semidom_semiring_numeral_div.semiring_char_0_linordered_semidom.semiring_1_semiring_char_0.semiring_numeral_semiring_1.numeral_semiring_numeral
                   m)
          else divmod_step _A n (divmod _A m (Bit0 n)));;

let rec less_eq_int
  x0 x1 = match x0, x1 with Neg k, Neg l -> less_eq_num l k
    | Neg k, Pos l -> true
    | Neg k, Zero_int -> true
    | Pos k, Neg l -> false
    | Pos k, Pos l -> less_eq_num k l
    | Pos k, Zero_int -> false
    | Zero_int, Neg l -> false
    | Zero_int, Pos l -> true
    | Zero_int, Zero_int -> true;;

let rec fst (x1, x2) = x1;;

let plus_int = ({plus = plus_inta} : int plus);;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : int semigroup_add);;

let cancel_semigroup_add_int =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_int} :
    int cancel_semigroup_add);;

let ab_semigroup_add_int =
  ({semigroup_add_ab_semigroup_add = semigroup_add_int} :
    int ab_semigroup_add);;

let minus_int = ({minus = minus_inta} : int minus);;

let cancel_ab_semigroup_add_int =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int;
     minus_cancel_ab_semigroup_add = minus_int}
    : int cancel_ab_semigroup_add);;

let zero_int = ({zero = Zero_int} : int zero);;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    int monoid_add);;

let comm_monoid_add_int =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int;
     monoid_add_comm_monoid_add = monoid_add_int}
    : int comm_monoid_add);;

let cancel_comm_monoid_add_int =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_int;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
    : int cancel_comm_monoid_add);;

let mult_zero_int =
  ({times_mult_zero = times_int; zero_mult_zero = zero_int} : int mult_zero);;

let semigroup_mult_int =
  ({times_semigroup_mult = times_int} : int semigroup_mult);;

let semiring_int =
  ({ab_semigroup_add_semiring = ab_semigroup_add_int;
     semigroup_mult_semiring = semigroup_mult_int}
    : int semiring);;

let semiring_0_int =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_int;
     mult_zero_semiring_0 = mult_zero_int; semiring_semiring_0 = semiring_int}
    : int semiring_0);;

let semiring_0_cancel_int =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int;
     semiring_0_semiring_0_cancel = semiring_0_int}
    : int semiring_0_cancel);;

let ab_semigroup_mult_int =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
    int ab_semigroup_mult);;

let comm_semiring_int =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int;
     semiring_comm_semiring = semiring_int}
    : int comm_semiring);;

let comm_semiring_0_int =
  ({comm_semiring_comm_semiring_0 = comm_semiring_int;
     semiring_0_comm_semiring_0 = semiring_0_int}
    : int comm_semiring_0);;

let comm_semiring_0_cancel_int =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
    : int comm_semiring_0_cancel);;

let power_int = ({one_power = one_int; times_power = times_int} : int power);;

let monoid_mult_int =
  ({semigroup_mult_monoid_mult = semigroup_mult_int;
     power_monoid_mult = power_int}
    : int monoid_mult);;

let numeral_int =
  ({one_numeral = one_int; semigroup_add_numeral = semigroup_add_int} :
    int numeral);;

let semiring_numeral_int =
  ({monoid_mult_semiring_numeral = monoid_mult_int;
     numeral_semiring_numeral = numeral_int;
     semiring_semiring_numeral = semiring_int}
    : int semiring_numeral);;

let zero_neq_one_int =
  ({one_zero_neq_one = one_int; zero_zero_neq_one = zero_int} :
    int zero_neq_one);;

let semiring_1_int =
  ({semiring_numeral_semiring_1 = semiring_numeral_int;
     semiring_0_semiring_1 = semiring_0_int;
     zero_neq_one_semiring_1 = zero_neq_one_int}
    : int semiring_1);;

let semiring_1_cancel_int =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int;
     semiring_1_semiring_1_cancel = semiring_1_int}
    : int semiring_1_cancel);;

let comm_monoid_mult_int =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int;
     monoid_mult_comm_monoid_mult = monoid_mult_int;
     dvd_comm_monoid_mult = dvd_int}
    : int comm_monoid_mult);;

let comm_semiring_1_int =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_int;
     semiring_1_comm_semiring_1 = semiring_1_int}
    : int comm_semiring_1);;

let comm_semiring_1_cancel_int =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
    : int comm_semiring_1_cancel);;

let comm_semiring_1_diff_distrib_int =
  ({comm_semiring_1_cancel_comm_semiring_1_diff_distrib =
      comm_semiring_1_cancel_int}
    : int comm_semiring_1_diff_distrib);;

let semiring_parity_int =
  ({comm_semiring_1_diff_distrib_semiring_parity =
      comm_semiring_1_diff_distrib_int}
    : int semiring_parity);;

let semiring_no_zero_divisors_int =
  ({semiring_0_semiring_no_zero_divisors = semiring_0_int} :
    int semiring_no_zero_divisors);;

let semidom_int =
  ({comm_semiring_1_diff_distrib_semidom = comm_semiring_1_diff_distrib_int;
     semiring_no_zero_divisors_semidom = semiring_no_zero_divisors_int}
    : int semidom);;

let ord_int = ({less_eq = less_eq_int; less = less_int} : int ord);;

let preorder_int = ({ord_preorder = ord_int} : int preorder);;

let order_int = ({preorder_order = preorder_int} : int order);;

let ordered_ab_semigroup_add_int =
  ({ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_int;
     order_ordered_ab_semigroup_add = order_int}
    : int ordered_ab_semigroup_add);;

let ordered_semiring_int =
  ({comm_monoid_add_ordered_semiring = comm_monoid_add_int;
     ordered_ab_semigroup_add_ordered_semiring = ordered_ab_semigroup_add_int;
     semiring_ordered_semiring = semiring_int}
    : int ordered_semiring);;

let ordered_cancel_semiring_int =
  ({ordered_semiring_ordered_cancel_semiring = ordered_semiring_int;
     semiring_0_cancel_ordered_cancel_semiring = semiring_0_cancel_int}
    : int ordered_cancel_semiring);;

let ordered_comm_semiring_int =
  ({comm_semiring_0_ordered_comm_semiring = comm_semiring_0_int;
     ordered_semiring_ordered_comm_semiring = ordered_semiring_int}
    : int ordered_comm_semiring);;

let ordered_cancel_comm_semiring_int =
  ({comm_semiring_0_cancel_ordered_cancel_comm_semiring =
      comm_semiring_0_cancel_int;
     ordered_cancel_semiring_ordered_cancel_comm_semiring =
       ordered_cancel_semiring_int;
     ordered_comm_semiring_ordered_cancel_comm_semiring =
       ordered_comm_semiring_int}
    : int ordered_cancel_comm_semiring);;

let ordered_cancel_ab_semigroup_add_int =
  ({cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
      cancel_ab_semigroup_add_int;
     ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
       ordered_ab_semigroup_add_int}
    : int ordered_cancel_ab_semigroup_add);;

let ordered_ab_semigroup_add_imp_le_int =
  ({ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
      ordered_cancel_ab_semigroup_add_int}
    : int ordered_ab_semigroup_add_imp_le);;

let linorder_int = ({order_linorder = order_int} : int linorder);;

let linordered_ab_semigroup_add_int =
  ({ordered_ab_semigroup_add_linordered_ab_semigroup_add =
      ordered_ab_semigroup_add_int;
     linorder_linordered_ab_semigroup_add = linorder_int}
    : int linordered_ab_semigroup_add);;

let linordered_cancel_ab_semigroup_add_int =
  ({linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
      linordered_ab_semigroup_add_int;
     ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
       ordered_ab_semigroup_add_imp_le_int}
    : int linordered_cancel_ab_semigroup_add);;

let ordered_comm_monoid_add_int =
  ({comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_int;
     ordered_cancel_ab_semigroup_add_ordered_comm_monoid_add =
       ordered_cancel_ab_semigroup_add_int}
    : int ordered_comm_monoid_add);;

let linordered_semiring_int =
  ({linordered_cancel_ab_semigroup_add_linordered_semiring =
      linordered_cancel_ab_semigroup_add_int;
     ordered_comm_monoid_add_linordered_semiring = ordered_comm_monoid_add_int;
     ordered_cancel_semiring_linordered_semiring = ordered_cancel_semiring_int}
    : int linordered_semiring);;

let linordered_semiring_strict_int =
  ({linordered_semiring_linordered_semiring_strict = linordered_semiring_int} :
    int linordered_semiring_strict);;

let linordered_comm_semiring_strict_int =
  ({linordered_semiring_strict_linordered_comm_semiring_strict =
      linordered_semiring_strict_int;
     ordered_cancel_comm_semiring_linordered_comm_semiring_strict =
       ordered_cancel_comm_semiring_int}
    : int linordered_comm_semiring_strict);;

let semiring_char_0_int =
  ({semiring_1_semiring_char_0 = semiring_1_int} : int semiring_char_0);;

let linordered_semidom_int =
  ({semiring_char_0_linordered_semidom = semiring_char_0_int;
     linordered_comm_semiring_strict_linordered_semidom =
       linordered_comm_semiring_strict_int;
     semidom_linordered_semidom = semidom_int}
    : int linordered_semidom);;

let rec div_int () =
  ({dvd_div = dvd_int; div = div_inta; moda = mod_int} : int div)
and semiring_div_int () =
  ({div_semiring_div = (div_int ()); semidom_semiring_div = semidom_int} :
    int semiring_div)
and semiring_div_parity_int () =
  ({semiring_div_semiring_div_parity = (semiring_div_int ());
     semiring_parity_semiring_div_parity = semiring_parity_int}
    : int semiring_div_parity)
and semiring_numeral_div_int () =
  ({semiring_div_parity_semiring_numeral_div = (semiring_div_parity_int ());
     linordered_semidom_semiring_numeral_div = linordered_semidom_int}
    : int semiring_numeral_div)
and divmod_abs
  j ja = match j, ja with Zero_int, j -> (Zero_int, Zero_int)
    | j, Zero_int -> (Zero_int, abs_int j)
    | Pos k, Neg l -> divmod (semiring_numeral_div_int ()) k l
    | Neg k, Pos l -> divmod (semiring_numeral_div_int ()) k l
    | Neg k, Neg l -> divmod (semiring_numeral_div_int ()) k l
    | Pos k, Pos l -> divmod (semiring_numeral_div_int ()) k l
and divmod_int
  k l = (if equal_inta k Zero_int then (Zero_int, Zero_int)
          else (if equal_inta l Zero_int then (Zero_int, k)
                 else apsnd (times_inta (sgn_int l))
                        (if equal_inta (sgn_int k) (sgn_int l)
                          then divmod_abs k l
                          else let (r, s) = divmod_abs k l in
                               (if equal_inta s Zero_int
                                 then (uminus_int r, Zero_int)
                                 else (minus_inta (uminus_int r) (Pos One),
minus_inta (abs_int l) s)))))
and div_inta a b = fst (divmod_int a b)
and mod_int a b = snd (divmod_int a b);;
let div_int = div_int ();;
let semiring_div_int = semiring_div_int ();;
let semiring_div_parity_int = semiring_div_parity_int ();;
let semiring_numeral_div_int = semiring_numeral_div_int ();;

type nat = Zero_nat | Suc of nat;;

let rec equal_nata
  x0 x1 = match x0, x1 with Zero_nat, Suc x2 -> false
    | Suc x2, Zero_nat -> false
    | Suc x2, Suc y2 -> equal_nata x2 y2
    | Zero_nat, Zero_nat -> true;;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec less_eq_nat
  x0 n = match x0, n with Suc m, n -> less_nat m n
    | Zero_nat, n -> true
and less_nat
  m x1 = match m, x1 with m, Suc n -> less_eq_nat m n
    | n, Zero_nat -> false;;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let rec eq _A a b = equal _A a b;;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

type uop = BvPOS | BvNEG | BvNOT | BvCOMP;;

let rec equal_uop
  x0 x1 = match x0, x1 with BvNOT, BvCOMP -> false
    | BvCOMP, BvNOT -> false
    | BvNEG, BvCOMP -> false
    | BvCOMP, BvNEG -> false
    | BvNEG, BvNOT -> false
    | BvNOT, BvNEG -> false
    | BvPOS, BvCOMP -> false
    | BvCOMP, BvPOS -> false
    | BvPOS, BvNOT -> false
    | BvNOT, BvPOS -> false
    | BvPOS, BvNEG -> false
    | BvNEG, BvPOS -> false
    | BvCOMP, BvCOMP -> true
    | BvNOT, BvNOT -> true
    | BvNEG, BvNEG -> true
    | BvPOS, BvPOS -> true;;

type lop = BvsLT | BvsLTE | BvsGT | BvsGTE | BvsEQ | BvsNEQ | BvsLAND | BvsLOR;;

let rec equal_lop
  x0 x1 = match x0, x1 with BvsLAND, BvsLOR -> false
    | BvsLOR, BvsLAND -> false
    | BvsNEQ, BvsLOR -> false
    | BvsLOR, BvsNEQ -> false
    | BvsNEQ, BvsLAND -> false
    | BvsLAND, BvsNEQ -> false
    | BvsEQ, BvsLOR -> false
    | BvsLOR, BvsEQ -> false
    | BvsEQ, BvsLAND -> false
    | BvsLAND, BvsEQ -> false
    | BvsEQ, BvsNEQ -> false
    | BvsNEQ, BvsEQ -> false
    | BvsGTE, BvsLOR -> false
    | BvsLOR, BvsGTE -> false
    | BvsGTE, BvsLAND -> false
    | BvsLAND, BvsGTE -> false
    | BvsGTE, BvsNEQ -> false
    | BvsNEQ, BvsGTE -> false
    | BvsGTE, BvsEQ -> false
    | BvsEQ, BvsGTE -> false
    | BvsGT, BvsLOR -> false
    | BvsLOR, BvsGT -> false
    | BvsGT, BvsLAND -> false
    | BvsLAND, BvsGT -> false
    | BvsGT, BvsNEQ -> false
    | BvsNEQ, BvsGT -> false
    | BvsGT, BvsEQ -> false
    | BvsEQ, BvsGT -> false
    | BvsGT, BvsGTE -> false
    | BvsGTE, BvsGT -> false
    | BvsLTE, BvsLOR -> false
    | BvsLOR, BvsLTE -> false
    | BvsLTE, BvsLAND -> false
    | BvsLAND, BvsLTE -> false
    | BvsLTE, BvsNEQ -> false
    | BvsNEQ, BvsLTE -> false
    | BvsLTE, BvsEQ -> false
    | BvsEQ, BvsLTE -> false
    | BvsLTE, BvsGTE -> false
    | BvsGTE, BvsLTE -> false
    | BvsLTE, BvsGT -> false
    | BvsGT, BvsLTE -> false
    | BvsLT, BvsLOR -> false
    | BvsLOR, BvsLT -> false
    | BvsLT, BvsLAND -> false
    | BvsLAND, BvsLT -> false
    | BvsLT, BvsNEQ -> false
    | BvsNEQ, BvsLT -> false
    | BvsLT, BvsEQ -> false
    | BvsEQ, BvsLT -> false
    | BvsLT, BvsGTE -> false
    | BvsGTE, BvsLT -> false
    | BvsLT, BvsGT -> false
    | BvsGT, BvsLT -> false
    | BvsLT, BvsLTE -> false
    | BvsLTE, BvsLT -> false
    | BvsLOR, BvsLOR -> true
    | BvsLAND, BvsLAND -> true
    | BvsNEQ, BvsNEQ -> true
    | BvsEQ, BvsEQ -> true
    | BvsGTE, BvsGTE -> true
    | BvsGT, BvsGT -> true
    | BvsLTE, BvsLTE -> true
    | BvsLT, BvsLT -> true;;

type bop = BvsMULT | BvsPLUS | BvsSUB | BvsDIV | BvsMOD | BvsAND | BvsOR |
  BvsXOR | BvsXNOR | BvsCONC;;

let rec equal_bop
  x0 x1 = match x0, x1 with BvsXNOR, BvsCONC -> false
    | BvsCONC, BvsXNOR -> false
    | BvsXOR, BvsCONC -> false
    | BvsCONC, BvsXOR -> false
    | BvsXOR, BvsXNOR -> false
    | BvsXNOR, BvsXOR -> false
    | BvsOR, BvsCONC -> false
    | BvsCONC, BvsOR -> false
    | BvsOR, BvsXNOR -> false
    | BvsXNOR, BvsOR -> false
    | BvsOR, BvsXOR -> false
    | BvsXOR, BvsOR -> false
    | BvsAND, BvsCONC -> false
    | BvsCONC, BvsAND -> false
    | BvsAND, BvsXNOR -> false
    | BvsXNOR, BvsAND -> false
    | BvsAND, BvsXOR -> false
    | BvsXOR, BvsAND -> false
    | BvsAND, BvsOR -> false
    | BvsOR, BvsAND -> false
    | BvsMOD, BvsCONC -> false
    | BvsCONC, BvsMOD -> false
    | BvsMOD, BvsXNOR -> false
    | BvsXNOR, BvsMOD -> false
    | BvsMOD, BvsXOR -> false
    | BvsXOR, BvsMOD -> false
    | BvsMOD, BvsOR -> false
    | BvsOR, BvsMOD -> false
    | BvsMOD, BvsAND -> false
    | BvsAND, BvsMOD -> false
    | BvsDIV, BvsCONC -> false
    | BvsCONC, BvsDIV -> false
    | BvsDIV, BvsXNOR -> false
    | BvsXNOR, BvsDIV -> false
    | BvsDIV, BvsXOR -> false
    | BvsXOR, BvsDIV -> false
    | BvsDIV, BvsOR -> false
    | BvsOR, BvsDIV -> false
    | BvsDIV, BvsAND -> false
    | BvsAND, BvsDIV -> false
    | BvsDIV, BvsMOD -> false
    | BvsMOD, BvsDIV -> false
    | BvsSUB, BvsCONC -> false
    | BvsCONC, BvsSUB -> false
    | BvsSUB, BvsXNOR -> false
    | BvsXNOR, BvsSUB -> false
    | BvsSUB, BvsXOR -> false
    | BvsXOR, BvsSUB -> false
    | BvsSUB, BvsOR -> false
    | BvsOR, BvsSUB -> false
    | BvsSUB, BvsAND -> false
    | BvsAND, BvsSUB -> false
    | BvsSUB, BvsMOD -> false
    | BvsMOD, BvsSUB -> false
    | BvsSUB, BvsDIV -> false
    | BvsDIV, BvsSUB -> false
    | BvsPLUS, BvsCONC -> false
    | BvsCONC, BvsPLUS -> false
    | BvsPLUS, BvsXNOR -> false
    | BvsXNOR, BvsPLUS -> false
    | BvsPLUS, BvsXOR -> false
    | BvsXOR, BvsPLUS -> false
    | BvsPLUS, BvsOR -> false
    | BvsOR, BvsPLUS -> false
    | BvsPLUS, BvsAND -> false
    | BvsAND, BvsPLUS -> false
    | BvsPLUS, BvsMOD -> false
    | BvsMOD, BvsPLUS -> false
    | BvsPLUS, BvsDIV -> false
    | BvsDIV, BvsPLUS -> false
    | BvsPLUS, BvsSUB -> false
    | BvsSUB, BvsPLUS -> false
    | BvsMULT, BvsCONC -> false
    | BvsCONC, BvsMULT -> false
    | BvsMULT, BvsXNOR -> false
    | BvsXNOR, BvsMULT -> false
    | BvsMULT, BvsXOR -> false
    | BvsXOR, BvsMULT -> false
    | BvsMULT, BvsOR -> false
    | BvsOR, BvsMULT -> false
    | BvsMULT, BvsAND -> false
    | BvsAND, BvsMULT -> false
    | BvsMULT, BvsMOD -> false
    | BvsMOD, BvsMULT -> false
    | BvsMULT, BvsDIV -> false
    | BvsDIV, BvsMULT -> false
    | BvsMULT, BvsSUB -> false
    | BvsSUB, BvsMULT -> false
    | BvsMULT, BvsPLUS -> false
    | BvsPLUS, BvsMULT -> false
    | BvsCONC, BvsCONC -> true
    | BvsXNOR, BvsXNOR -> true
    | BvsXOR, BvsXOR -> true
    | BvsOR, BvsOR -> true
    | BvsAND, BvsAND -> true
    | BvsMOD, BvsMOD -> true
    | BvsDIV, BvsDIV -> true
    | BvsSUB, BvsSUB -> true
    | BvsPLUS, BvsPLUS -> true
    | BvsMULT, BvsMULT -> true;;

type name = X | Y | Z | CLK | I1 | O1 | R1 | R2 | R3 | R4 | R5 | W1 | W2 | W3 |
  W4 | Sum_out | Carry_out | Carry_in | Ina | Inb | Bus_out | Bus0 | Bus1 | Bus2
  | Enable | Select | Data | Onea | Two | Three | Four | I1a | O1a | W1a | I2 |
  O2 | Xi | Yi | Q | Qa | R | S;;

let rec equal_namea
  x0 x1 = match x0, x1 with R, S -> false
    | S, R -> false
    | Qa, S -> false
    | S, Qa -> false
    | Qa, R -> false
    | R, Qa -> false
    | Q, S -> false
    | S, Q -> false
    | Q, R -> false
    | R, Q -> false
    | Q, Qa -> false
    | Qa, Q -> false
    | Yi, S -> false
    | S, Yi -> false
    | Yi, R -> false
    | R, Yi -> false
    | Yi, Qa -> false
    | Qa, Yi -> false
    | Yi, Q -> false
    | Q, Yi -> false
    | Xi, S -> false
    | S, Xi -> false
    | Xi, R -> false
    | R, Xi -> false
    | Xi, Qa -> false
    | Qa, Xi -> false
    | Xi, Q -> false
    | Q, Xi -> false
    | Xi, Yi -> false
    | Yi, Xi -> false
    | O2, S -> false
    | S, O2 -> false
    | O2, R -> false
    | R, O2 -> false
    | O2, Qa -> false
    | Qa, O2 -> false
    | O2, Q -> false
    | Q, O2 -> false
    | O2, Yi -> false
    | Yi, O2 -> false
    | O2, Xi -> false
    | Xi, O2 -> false
    | I2, S -> false
    | S, I2 -> false
    | I2, R -> false
    | R, I2 -> false
    | I2, Qa -> false
    | Qa, I2 -> false
    | I2, Q -> false
    | Q, I2 -> false
    | I2, Yi -> false
    | Yi, I2 -> false
    | I2, Xi -> false
    | Xi, I2 -> false
    | I2, O2 -> false
    | O2, I2 -> false
    | W1a, S -> false
    | S, W1a -> false
    | W1a, R -> false
    | R, W1a -> false
    | W1a, Qa -> false
    | Qa, W1a -> false
    | W1a, Q -> false
    | Q, W1a -> false
    | W1a, Yi -> false
    | Yi, W1a -> false
    | W1a, Xi -> false
    | Xi, W1a -> false
    | W1a, O2 -> false
    | O2, W1a -> false
    | W1a, I2 -> false
    | I2, W1a -> false
    | O1a, S -> false
    | S, O1a -> false
    | O1a, R -> false
    | R, O1a -> false
    | O1a, Qa -> false
    | Qa, O1a -> false
    | O1a, Q -> false
    | Q, O1a -> false
    | O1a, Yi -> false
    | Yi, O1a -> false
    | O1a, Xi -> false
    | Xi, O1a -> false
    | O1a, O2 -> false
    | O2, O1a -> false
    | O1a, I2 -> false
    | I2, O1a -> false
    | O1a, W1a -> false
    | W1a, O1a -> false
    | I1a, S -> false
    | S, I1a -> false
    | I1a, R -> false
    | R, I1a -> false
    | I1a, Qa -> false
    | Qa, I1a -> false
    | I1a, Q -> false
    | Q, I1a -> false
    | I1a, Yi -> false
    | Yi, I1a -> false
    | I1a, Xi -> false
    | Xi, I1a -> false
    | I1a, O2 -> false
    | O2, I1a -> false
    | I1a, I2 -> false
    | I2, I1a -> false
    | I1a, W1a -> false
    | W1a, I1a -> false
    | I1a, O1a -> false
    | O1a, I1a -> false
    | Four, S -> false
    | S, Four -> false
    | Four, R -> false
    | R, Four -> false
    | Four, Qa -> false
    | Qa, Four -> false
    | Four, Q -> false
    | Q, Four -> false
    | Four, Yi -> false
    | Yi, Four -> false
    | Four, Xi -> false
    | Xi, Four -> false
    | Four, O2 -> false
    | O2, Four -> false
    | Four, I2 -> false
    | I2, Four -> false
    | Four, W1a -> false
    | W1a, Four -> false
    | Four, O1a -> false
    | O1a, Four -> false
    | Four, I1a -> false
    | I1a, Four -> false
    | Three, S -> false
    | S, Three -> false
    | Three, R -> false
    | R, Three -> false
    | Three, Qa -> false
    | Qa, Three -> false
    | Three, Q -> false
    | Q, Three -> false
    | Three, Yi -> false
    | Yi, Three -> false
    | Three, Xi -> false
    | Xi, Three -> false
    | Three, O2 -> false
    | O2, Three -> false
    | Three, I2 -> false
    | I2, Three -> false
    | Three, W1a -> false
    | W1a, Three -> false
    | Three, O1a -> false
    | O1a, Three -> false
    | Three, I1a -> false
    | I1a, Three -> false
    | Three, Four -> false
    | Four, Three -> false
    | Two, S -> false
    | S, Two -> false
    | Two, R -> false
    | R, Two -> false
    | Two, Qa -> false
    | Qa, Two -> false
    | Two, Q -> false
    | Q, Two -> false
    | Two, Yi -> false
    | Yi, Two -> false
    | Two, Xi -> false
    | Xi, Two -> false
    | Two, O2 -> false
    | O2, Two -> false
    | Two, I2 -> false
    | I2, Two -> false
    | Two, W1a -> false
    | W1a, Two -> false
    | Two, O1a -> false
    | O1a, Two -> false
    | Two, I1a -> false
    | I1a, Two -> false
    | Two, Four -> false
    | Four, Two -> false
    | Two, Three -> false
    | Three, Two -> false
    | Onea, S -> false
    | S, Onea -> false
    | Onea, R -> false
    | R, Onea -> false
    | Onea, Qa -> false
    | Qa, Onea -> false
    | Onea, Q -> false
    | Q, Onea -> false
    | Onea, Yi -> false
    | Yi, Onea -> false
    | Onea, Xi -> false
    | Xi, Onea -> false
    | Onea, O2 -> false
    | O2, Onea -> false
    | Onea, I2 -> false
    | I2, Onea -> false
    | Onea, W1a -> false
    | W1a, Onea -> false
    | Onea, O1a -> false
    | O1a, Onea -> false
    | Onea, I1a -> false
    | I1a, Onea -> false
    | Onea, Four -> false
    | Four, Onea -> false
    | Onea, Three -> false
    | Three, Onea -> false
    | Onea, Two -> false
    | Two, Onea -> false
    | Data, S -> false
    | S, Data -> false
    | Data, R -> false
    | R, Data -> false
    | Data, Qa -> false
    | Qa, Data -> false
    | Data, Q -> false
    | Q, Data -> false
    | Data, Yi -> false
    | Yi, Data -> false
    | Data, Xi -> false
    | Xi, Data -> false
    | Data, O2 -> false
    | O2, Data -> false
    | Data, I2 -> false
    | I2, Data -> false
    | Data, W1a -> false
    | W1a, Data -> false
    | Data, O1a -> false
    | O1a, Data -> false
    | Data, I1a -> false
    | I1a, Data -> false
    | Data, Four -> false
    | Four, Data -> false
    | Data, Three -> false
    | Three, Data -> false
    | Data, Two -> false
    | Two, Data -> false
    | Data, Onea -> false
    | Onea, Data -> false
    | Select, S -> false
    | S, Select -> false
    | Select, R -> false
    | R, Select -> false
    | Select, Qa -> false
    | Qa, Select -> false
    | Select, Q -> false
    | Q, Select -> false
    | Select, Yi -> false
    | Yi, Select -> false
    | Select, Xi -> false
    | Xi, Select -> false
    | Select, O2 -> false
    | O2, Select -> false
    | Select, I2 -> false
    | I2, Select -> false
    | Select, W1a -> false
    | W1a, Select -> false
    | Select, O1a -> false
    | O1a, Select -> false
    | Select, I1a -> false
    | I1a, Select -> false
    | Select, Four -> false
    | Four, Select -> false
    | Select, Three -> false
    | Three, Select -> false
    | Select, Two -> false
    | Two, Select -> false
    | Select, Onea -> false
    | Onea, Select -> false
    | Select, Data -> false
    | Data, Select -> false
    | Enable, S -> false
    | S, Enable -> false
    | Enable, R -> false
    | R, Enable -> false
    | Enable, Qa -> false
    | Qa, Enable -> false
    | Enable, Q -> false
    | Q, Enable -> false
    | Enable, Yi -> false
    | Yi, Enable -> false
    | Enable, Xi -> false
    | Xi, Enable -> false
    | Enable, O2 -> false
    | O2, Enable -> false
    | Enable, I2 -> false
    | I2, Enable -> false
    | Enable, W1a -> false
    | W1a, Enable -> false
    | Enable, O1a -> false
    | O1a, Enable -> false
    | Enable, I1a -> false
    | I1a, Enable -> false
    | Enable, Four -> false
    | Four, Enable -> false
    | Enable, Three -> false
    | Three, Enable -> false
    | Enable, Two -> false
    | Two, Enable -> false
    | Enable, Onea -> false
    | Onea, Enable -> false
    | Enable, Data -> false
    | Data, Enable -> false
    | Enable, Select -> false
    | Select, Enable -> false
    | Bus2, S -> false
    | S, Bus2 -> false
    | Bus2, R -> false
    | R, Bus2 -> false
    | Bus2, Qa -> false
    | Qa, Bus2 -> false
    | Bus2, Q -> false
    | Q, Bus2 -> false
    | Bus2, Yi -> false
    | Yi, Bus2 -> false
    | Bus2, Xi -> false
    | Xi, Bus2 -> false
    | Bus2, O2 -> false
    | O2, Bus2 -> false
    | Bus2, I2 -> false
    | I2, Bus2 -> false
    | Bus2, W1a -> false
    | W1a, Bus2 -> false
    | Bus2, O1a -> false
    | O1a, Bus2 -> false
    | Bus2, I1a -> false
    | I1a, Bus2 -> false
    | Bus2, Four -> false
    | Four, Bus2 -> false
    | Bus2, Three -> false
    | Three, Bus2 -> false
    | Bus2, Two -> false
    | Two, Bus2 -> false
    | Bus2, Onea -> false
    | Onea, Bus2 -> false
    | Bus2, Data -> false
    | Data, Bus2 -> false
    | Bus2, Select -> false
    | Select, Bus2 -> false
    | Bus2, Enable -> false
    | Enable, Bus2 -> false
    | Bus1, S -> false
    | S, Bus1 -> false
    | Bus1, R -> false
    | R, Bus1 -> false
    | Bus1, Qa -> false
    | Qa, Bus1 -> false
    | Bus1, Q -> false
    | Q, Bus1 -> false
    | Bus1, Yi -> false
    | Yi, Bus1 -> false
    | Bus1, Xi -> false
    | Xi, Bus1 -> false
    | Bus1, O2 -> false
    | O2, Bus1 -> false
    | Bus1, I2 -> false
    | I2, Bus1 -> false
    | Bus1, W1a -> false
    | W1a, Bus1 -> false
    | Bus1, O1a -> false
    | O1a, Bus1 -> false
    | Bus1, I1a -> false
    | I1a, Bus1 -> false
    | Bus1, Four -> false
    | Four, Bus1 -> false
    | Bus1, Three -> false
    | Three, Bus1 -> false
    | Bus1, Two -> false
    | Two, Bus1 -> false
    | Bus1, Onea -> false
    | Onea, Bus1 -> false
    | Bus1, Data -> false
    | Data, Bus1 -> false
    | Bus1, Select -> false
    | Select, Bus1 -> false
    | Bus1, Enable -> false
    | Enable, Bus1 -> false
    | Bus1, Bus2 -> false
    | Bus2, Bus1 -> false
    | Bus0, S -> false
    | S, Bus0 -> false
    | Bus0, R -> false
    | R, Bus0 -> false
    | Bus0, Qa -> false
    | Qa, Bus0 -> false
    | Bus0, Q -> false
    | Q, Bus0 -> false
    | Bus0, Yi -> false
    | Yi, Bus0 -> false
    | Bus0, Xi -> false
    | Xi, Bus0 -> false
    | Bus0, O2 -> false
    | O2, Bus0 -> false
    | Bus0, I2 -> false
    | I2, Bus0 -> false
    | Bus0, W1a -> false
    | W1a, Bus0 -> false
    | Bus0, O1a -> false
    | O1a, Bus0 -> false
    | Bus0, I1a -> false
    | I1a, Bus0 -> false
    | Bus0, Four -> false
    | Four, Bus0 -> false
    | Bus0, Three -> false
    | Three, Bus0 -> false
    | Bus0, Two -> false
    | Two, Bus0 -> false
    | Bus0, Onea -> false
    | Onea, Bus0 -> false
    | Bus0, Data -> false
    | Data, Bus0 -> false
    | Bus0, Select -> false
    | Select, Bus0 -> false
    | Bus0, Enable -> false
    | Enable, Bus0 -> false
    | Bus0, Bus2 -> false
    | Bus2, Bus0 -> false
    | Bus0, Bus1 -> false
    | Bus1, Bus0 -> false
    | Bus_out, S -> false
    | S, Bus_out -> false
    | Bus_out, R -> false
    | R, Bus_out -> false
    | Bus_out, Qa -> false
    | Qa, Bus_out -> false
    | Bus_out, Q -> false
    | Q, Bus_out -> false
    | Bus_out, Yi -> false
    | Yi, Bus_out -> false
    | Bus_out, Xi -> false
    | Xi, Bus_out -> false
    | Bus_out, O2 -> false
    | O2, Bus_out -> false
    | Bus_out, I2 -> false
    | I2, Bus_out -> false
    | Bus_out, W1a -> false
    | W1a, Bus_out -> false
    | Bus_out, O1a -> false
    | O1a, Bus_out -> false
    | Bus_out, I1a -> false
    | I1a, Bus_out -> false
    | Bus_out, Four -> false
    | Four, Bus_out -> false
    | Bus_out, Three -> false
    | Three, Bus_out -> false
    | Bus_out, Two -> false
    | Two, Bus_out -> false
    | Bus_out, Onea -> false
    | Onea, Bus_out -> false
    | Bus_out, Data -> false
    | Data, Bus_out -> false
    | Bus_out, Select -> false
    | Select, Bus_out -> false
    | Bus_out, Enable -> false
    | Enable, Bus_out -> false
    | Bus_out, Bus2 -> false
    | Bus2, Bus_out -> false
    | Bus_out, Bus1 -> false
    | Bus1, Bus_out -> false
    | Bus_out, Bus0 -> false
    | Bus0, Bus_out -> false
    | Inb, S -> false
    | S, Inb -> false
    | Inb, R -> false
    | R, Inb -> false
    | Inb, Qa -> false
    | Qa, Inb -> false
    | Inb, Q -> false
    | Q, Inb -> false
    | Inb, Yi -> false
    | Yi, Inb -> false
    | Inb, Xi -> false
    | Xi, Inb -> false
    | Inb, O2 -> false
    | O2, Inb -> false
    | Inb, I2 -> false
    | I2, Inb -> false
    | Inb, W1a -> false
    | W1a, Inb -> false
    | Inb, O1a -> false
    | O1a, Inb -> false
    | Inb, I1a -> false
    | I1a, Inb -> false
    | Inb, Four -> false
    | Four, Inb -> false
    | Inb, Three -> false
    | Three, Inb -> false
    | Inb, Two -> false
    | Two, Inb -> false
    | Inb, Onea -> false
    | Onea, Inb -> false
    | Inb, Data -> false
    | Data, Inb -> false
    | Inb, Select -> false
    | Select, Inb -> false
    | Inb, Enable -> false
    | Enable, Inb -> false
    | Inb, Bus2 -> false
    | Bus2, Inb -> false
    | Inb, Bus1 -> false
    | Bus1, Inb -> false
    | Inb, Bus0 -> false
    | Bus0, Inb -> false
    | Inb, Bus_out -> false
    | Bus_out, Inb -> false
    | Ina, S -> false
    | S, Ina -> false
    | Ina, R -> false
    | R, Ina -> false
    | Ina, Qa -> false
    | Qa, Ina -> false
    | Ina, Q -> false
    | Q, Ina -> false
    | Ina, Yi -> false
    | Yi, Ina -> false
    | Ina, Xi -> false
    | Xi, Ina -> false
    | Ina, O2 -> false
    | O2, Ina -> false
    | Ina, I2 -> false
    | I2, Ina -> false
    | Ina, W1a -> false
    | W1a, Ina -> false
    | Ina, O1a -> false
    | O1a, Ina -> false
    | Ina, I1a -> false
    | I1a, Ina -> false
    | Ina, Four -> false
    | Four, Ina -> false
    | Ina, Three -> false
    | Three, Ina -> false
    | Ina, Two -> false
    | Two, Ina -> false
    | Ina, Onea -> false
    | Onea, Ina -> false
    | Ina, Data -> false
    | Data, Ina -> false
    | Ina, Select -> false
    | Select, Ina -> false
    | Ina, Enable -> false
    | Enable, Ina -> false
    | Ina, Bus2 -> false
    | Bus2, Ina -> false
    | Ina, Bus1 -> false
    | Bus1, Ina -> false
    | Ina, Bus0 -> false
    | Bus0, Ina -> false
    | Ina, Bus_out -> false
    | Bus_out, Ina -> false
    | Ina, Inb -> false
    | Inb, Ina -> false
    | Carry_in, S -> false
    | S, Carry_in -> false
    | Carry_in, R -> false
    | R, Carry_in -> false
    | Carry_in, Qa -> false
    | Qa, Carry_in -> false
    | Carry_in, Q -> false
    | Q, Carry_in -> false
    | Carry_in, Yi -> false
    | Yi, Carry_in -> false
    | Carry_in, Xi -> false
    | Xi, Carry_in -> false
    | Carry_in, O2 -> false
    | O2, Carry_in -> false
    | Carry_in, I2 -> false
    | I2, Carry_in -> false
    | Carry_in, W1a -> false
    | W1a, Carry_in -> false
    | Carry_in, O1a -> false
    | O1a, Carry_in -> false
    | Carry_in, I1a -> false
    | I1a, Carry_in -> false
    | Carry_in, Four -> false
    | Four, Carry_in -> false
    | Carry_in, Three -> false
    | Three, Carry_in -> false
    | Carry_in, Two -> false
    | Two, Carry_in -> false
    | Carry_in, Onea -> false
    | Onea, Carry_in -> false
    | Carry_in, Data -> false
    | Data, Carry_in -> false
    | Carry_in, Select -> false
    | Select, Carry_in -> false
    | Carry_in, Enable -> false
    | Enable, Carry_in -> false
    | Carry_in, Bus2 -> false
    | Bus2, Carry_in -> false
    | Carry_in, Bus1 -> false
    | Bus1, Carry_in -> false
    | Carry_in, Bus0 -> false
    | Bus0, Carry_in -> false
    | Carry_in, Bus_out -> false
    | Bus_out, Carry_in -> false
    | Carry_in, Inb -> false
    | Inb, Carry_in -> false
    | Carry_in, Ina -> false
    | Ina, Carry_in -> false
    | Carry_out, S -> false
    | S, Carry_out -> false
    | Carry_out, R -> false
    | R, Carry_out -> false
    | Carry_out, Qa -> false
    | Qa, Carry_out -> false
    | Carry_out, Q -> false
    | Q, Carry_out -> false
    | Carry_out, Yi -> false
    | Yi, Carry_out -> false
    | Carry_out, Xi -> false
    | Xi, Carry_out -> false
    | Carry_out, O2 -> false
    | O2, Carry_out -> false
    | Carry_out, I2 -> false
    | I2, Carry_out -> false
    | Carry_out, W1a -> false
    | W1a, Carry_out -> false
    | Carry_out, O1a -> false
    | O1a, Carry_out -> false
    | Carry_out, I1a -> false
    | I1a, Carry_out -> false
    | Carry_out, Four -> false
    | Four, Carry_out -> false
    | Carry_out, Three -> false
    | Three, Carry_out -> false
    | Carry_out, Two -> false
    | Two, Carry_out -> false
    | Carry_out, Onea -> false
    | Onea, Carry_out -> false
    | Carry_out, Data -> false
    | Data, Carry_out -> false
    | Carry_out, Select -> false
    | Select, Carry_out -> false
    | Carry_out, Enable -> false
    | Enable, Carry_out -> false
    | Carry_out, Bus2 -> false
    | Bus2, Carry_out -> false
    | Carry_out, Bus1 -> false
    | Bus1, Carry_out -> false
    | Carry_out, Bus0 -> false
    | Bus0, Carry_out -> false
    | Carry_out, Bus_out -> false
    | Bus_out, Carry_out -> false
    | Carry_out, Inb -> false
    | Inb, Carry_out -> false
    | Carry_out, Ina -> false
    | Ina, Carry_out -> false
    | Carry_out, Carry_in -> false
    | Carry_in, Carry_out -> false
    | Sum_out, S -> false
    | S, Sum_out -> false
    | Sum_out, R -> false
    | R, Sum_out -> false
    | Sum_out, Qa -> false
    | Qa, Sum_out -> false
    | Sum_out, Q -> false
    | Q, Sum_out -> false
    | Sum_out, Yi -> false
    | Yi, Sum_out -> false
    | Sum_out, Xi -> false
    | Xi, Sum_out -> false
    | Sum_out, O2 -> false
    | O2, Sum_out -> false
    | Sum_out, I2 -> false
    | I2, Sum_out -> false
    | Sum_out, W1a -> false
    | W1a, Sum_out -> false
    | Sum_out, O1a -> false
    | O1a, Sum_out -> false
    | Sum_out, I1a -> false
    | I1a, Sum_out -> false
    | Sum_out, Four -> false
    | Four, Sum_out -> false
    | Sum_out, Three -> false
    | Three, Sum_out -> false
    | Sum_out, Two -> false
    | Two, Sum_out -> false
    | Sum_out, Onea -> false
    | Onea, Sum_out -> false
    | Sum_out, Data -> false
    | Data, Sum_out -> false
    | Sum_out, Select -> false
    | Select, Sum_out -> false
    | Sum_out, Enable -> false
    | Enable, Sum_out -> false
    | Sum_out, Bus2 -> false
    | Bus2, Sum_out -> false
    | Sum_out, Bus1 -> false
    | Bus1, Sum_out -> false
    | Sum_out, Bus0 -> false
    | Bus0, Sum_out -> false
    | Sum_out, Bus_out -> false
    | Bus_out, Sum_out -> false
    | Sum_out, Inb -> false
    | Inb, Sum_out -> false
    | Sum_out, Ina -> false
    | Ina, Sum_out -> false
    | Sum_out, Carry_in -> false
    | Carry_in, Sum_out -> false
    | Sum_out, Carry_out -> false
    | Carry_out, Sum_out -> false
    | W4, S -> false
    | S, W4 -> false
    | W4, R -> false
    | R, W4 -> false
    | W4, Qa -> false
    | Qa, W4 -> false
    | W4, Q -> false
    | Q, W4 -> false
    | W4, Yi -> false
    | Yi, W4 -> false
    | W4, Xi -> false
    | Xi, W4 -> false
    | W4, O2 -> false
    | O2, W4 -> false
    | W4, I2 -> false
    | I2, W4 -> false
    | W4, W1a -> false
    | W1a, W4 -> false
    | W4, O1a -> false
    | O1a, W4 -> false
    | W4, I1a -> false
    | I1a, W4 -> false
    | W4, Four -> false
    | Four, W4 -> false
    | W4, Three -> false
    | Three, W4 -> false
    | W4, Two -> false
    | Two, W4 -> false
    | W4, Onea -> false
    | Onea, W4 -> false
    | W4, Data -> false
    | Data, W4 -> false
    | W4, Select -> false
    | Select, W4 -> false
    | W4, Enable -> false
    | Enable, W4 -> false
    | W4, Bus2 -> false
    | Bus2, W4 -> false
    | W4, Bus1 -> false
    | Bus1, W4 -> false
    | W4, Bus0 -> false
    | Bus0, W4 -> false
    | W4, Bus_out -> false
    | Bus_out, W4 -> false
    | W4, Inb -> false
    | Inb, W4 -> false
    | W4, Ina -> false
    | Ina, W4 -> false
    | W4, Carry_in -> false
    | Carry_in, W4 -> false
    | W4, Carry_out -> false
    | Carry_out, W4 -> false
    | W4, Sum_out -> false
    | Sum_out, W4 -> false
    | W3, S -> false
    | S, W3 -> false
    | W3, R -> false
    | R, W3 -> false
    | W3, Qa -> false
    | Qa, W3 -> false
    | W3, Q -> false
    | Q, W3 -> false
    | W3, Yi -> false
    | Yi, W3 -> false
    | W3, Xi -> false
    | Xi, W3 -> false
    | W3, O2 -> false
    | O2, W3 -> false
    | W3, I2 -> false
    | I2, W3 -> false
    | W3, W1a -> false
    | W1a, W3 -> false
    | W3, O1a -> false
    | O1a, W3 -> false
    | W3, I1a -> false
    | I1a, W3 -> false
    | W3, Four -> false
    | Four, W3 -> false
    | W3, Three -> false
    | Three, W3 -> false
    | W3, Two -> false
    | Two, W3 -> false
    | W3, Onea -> false
    | Onea, W3 -> false
    | W3, Data -> false
    | Data, W3 -> false
    | W3, Select -> false
    | Select, W3 -> false
    | W3, Enable -> false
    | Enable, W3 -> false
    | W3, Bus2 -> false
    | Bus2, W3 -> false
    | W3, Bus1 -> false
    | Bus1, W3 -> false
    | W3, Bus0 -> false
    | Bus0, W3 -> false
    | W3, Bus_out -> false
    | Bus_out, W3 -> false
    | W3, Inb -> false
    | Inb, W3 -> false
    | W3, Ina -> false
    | Ina, W3 -> false
    | W3, Carry_in -> false
    | Carry_in, W3 -> false
    | W3, Carry_out -> false
    | Carry_out, W3 -> false
    | W3, Sum_out -> false
    | Sum_out, W3 -> false
    | W3, W4 -> false
    | W4, W3 -> false
    | W2, S -> false
    | S, W2 -> false
    | W2, R -> false
    | R, W2 -> false
    | W2, Qa -> false
    | Qa, W2 -> false
    | W2, Q -> false
    | Q, W2 -> false
    | W2, Yi -> false
    | Yi, W2 -> false
    | W2, Xi -> false
    | Xi, W2 -> false
    | W2, O2 -> false
    | O2, W2 -> false
    | W2, I2 -> false
    | I2, W2 -> false
    | W2, W1a -> false
    | W1a, W2 -> false
    | W2, O1a -> false
    | O1a, W2 -> false
    | W2, I1a -> false
    | I1a, W2 -> false
    | W2, Four -> false
    | Four, W2 -> false
    | W2, Three -> false
    | Three, W2 -> false
    | W2, Two -> false
    | Two, W2 -> false
    | W2, Onea -> false
    | Onea, W2 -> false
    | W2, Data -> false
    | Data, W2 -> false
    | W2, Select -> false
    | Select, W2 -> false
    | W2, Enable -> false
    | Enable, W2 -> false
    | W2, Bus2 -> false
    | Bus2, W2 -> false
    | W2, Bus1 -> false
    | Bus1, W2 -> false
    | W2, Bus0 -> false
    | Bus0, W2 -> false
    | W2, Bus_out -> false
    | Bus_out, W2 -> false
    | W2, Inb -> false
    | Inb, W2 -> false
    | W2, Ina -> false
    | Ina, W2 -> false
    | W2, Carry_in -> false
    | Carry_in, W2 -> false
    | W2, Carry_out -> false
    | Carry_out, W2 -> false
    | W2, Sum_out -> false
    | Sum_out, W2 -> false
    | W2, W4 -> false
    | W4, W2 -> false
    | W2, W3 -> false
    | W3, W2 -> false
    | W1, S -> false
    | S, W1 -> false
    | W1, R -> false
    | R, W1 -> false
    | W1, Qa -> false
    | Qa, W1 -> false
    | W1, Q -> false
    | Q, W1 -> false
    | W1, Yi -> false
    | Yi, W1 -> false
    | W1, Xi -> false
    | Xi, W1 -> false
    | W1, O2 -> false
    | O2, W1 -> false
    | W1, I2 -> false
    | I2, W1 -> false
    | W1, W1a -> false
    | W1a, W1 -> false
    | W1, O1a -> false
    | O1a, W1 -> false
    | W1, I1a -> false
    | I1a, W1 -> false
    | W1, Four -> false
    | Four, W1 -> false
    | W1, Three -> false
    | Three, W1 -> false
    | W1, Two -> false
    | Two, W1 -> false
    | W1, Onea -> false
    | Onea, W1 -> false
    | W1, Data -> false
    | Data, W1 -> false
    | W1, Select -> false
    | Select, W1 -> false
    | W1, Enable -> false
    | Enable, W1 -> false
    | W1, Bus2 -> false
    | Bus2, W1 -> false
    | W1, Bus1 -> false
    | Bus1, W1 -> false
    | W1, Bus0 -> false
    | Bus0, W1 -> false
    | W1, Bus_out -> false
    | Bus_out, W1 -> false
    | W1, Inb -> false
    | Inb, W1 -> false
    | W1, Ina -> false
    | Ina, W1 -> false
    | W1, Carry_in -> false
    | Carry_in, W1 -> false
    | W1, Carry_out -> false
    | Carry_out, W1 -> false
    | W1, Sum_out -> false
    | Sum_out, W1 -> false
    | W1, W4 -> false
    | W4, W1 -> false
    | W1, W3 -> false
    | W3, W1 -> false
    | W1, W2 -> false
    | W2, W1 -> false
    | R5, S -> false
    | S, R5 -> false
    | R5, R -> false
    | R, R5 -> false
    | R5, Qa -> false
    | Qa, R5 -> false
    | R5, Q -> false
    | Q, R5 -> false
    | R5, Yi -> false
    | Yi, R5 -> false
    | R5, Xi -> false
    | Xi, R5 -> false
    | R5, O2 -> false
    | O2, R5 -> false
    | R5, I2 -> false
    | I2, R5 -> false
    | R5, W1a -> false
    | W1a, R5 -> false
    | R5, O1a -> false
    | O1a, R5 -> false
    | R5, I1a -> false
    | I1a, R5 -> false
    | R5, Four -> false
    | Four, R5 -> false
    | R5, Three -> false
    | Three, R5 -> false
    | R5, Two -> false
    | Two, R5 -> false
    | R5, Onea -> false
    | Onea, R5 -> false
    | R5, Data -> false
    | Data, R5 -> false
    | R5, Select -> false
    | Select, R5 -> false
    | R5, Enable -> false
    | Enable, R5 -> false
    | R5, Bus2 -> false
    | Bus2, R5 -> false
    | R5, Bus1 -> false
    | Bus1, R5 -> false
    | R5, Bus0 -> false
    | Bus0, R5 -> false
    | R5, Bus_out -> false
    | Bus_out, R5 -> false
    | R5, Inb -> false
    | Inb, R5 -> false
    | R5, Ina -> false
    | Ina, R5 -> false
    | R5, Carry_in -> false
    | Carry_in, R5 -> false
    | R5, Carry_out -> false
    | Carry_out, R5 -> false
    | R5, Sum_out -> false
    | Sum_out, R5 -> false
    | R5, W4 -> false
    | W4, R5 -> false
    | R5, W3 -> false
    | W3, R5 -> false
    | R5, W2 -> false
    | W2, R5 -> false
    | R5, W1 -> false
    | W1, R5 -> false
    | R4, S -> false
    | S, R4 -> false
    | R4, R -> false
    | R, R4 -> false
    | R4, Qa -> false
    | Qa, R4 -> false
    | R4, Q -> false
    | Q, R4 -> false
    | R4, Yi -> false
    | Yi, R4 -> false
    | R4, Xi -> false
    | Xi, R4 -> false
    | R4, O2 -> false
    | O2, R4 -> false
    | R4, I2 -> false
    | I2, R4 -> false
    | R4, W1a -> false
    | W1a, R4 -> false
    | R4, O1a -> false
    | O1a, R4 -> false
    | R4, I1a -> false
    | I1a, R4 -> false
    | R4, Four -> false
    | Four, R4 -> false
    | R4, Three -> false
    | Three, R4 -> false
    | R4, Two -> false
    | Two, R4 -> false
    | R4, Onea -> false
    | Onea, R4 -> false
    | R4, Data -> false
    | Data, R4 -> false
    | R4, Select -> false
    | Select, R4 -> false
    | R4, Enable -> false
    | Enable, R4 -> false
    | R4, Bus2 -> false
    | Bus2, R4 -> false
    | R4, Bus1 -> false
    | Bus1, R4 -> false
    | R4, Bus0 -> false
    | Bus0, R4 -> false
    | R4, Bus_out -> false
    | Bus_out, R4 -> false
    | R4, Inb -> false
    | Inb, R4 -> false
    | R4, Ina -> false
    | Ina, R4 -> false
    | R4, Carry_in -> false
    | Carry_in, R4 -> false
    | R4, Carry_out -> false
    | Carry_out, R4 -> false
    | R4, Sum_out -> false
    | Sum_out, R4 -> false
    | R4, W4 -> false
    | W4, R4 -> false
    | R4, W3 -> false
    | W3, R4 -> false
    | R4, W2 -> false
    | W2, R4 -> false
    | R4, W1 -> false
    | W1, R4 -> false
    | R4, R5 -> false
    | R5, R4 -> false
    | R3, S -> false
    | S, R3 -> false
    | R3, R -> false
    | R, R3 -> false
    | R3, Qa -> false
    | Qa, R3 -> false
    | R3, Q -> false
    | Q, R3 -> false
    | R3, Yi -> false
    | Yi, R3 -> false
    | R3, Xi -> false
    | Xi, R3 -> false
    | R3, O2 -> false
    | O2, R3 -> false
    | R3, I2 -> false
    | I2, R3 -> false
    | R3, W1a -> false
    | W1a, R3 -> false
    | R3, O1a -> false
    | O1a, R3 -> false
    | R3, I1a -> false
    | I1a, R3 -> false
    | R3, Four -> false
    | Four, R3 -> false
    | R3, Three -> false
    | Three, R3 -> false
    | R3, Two -> false
    | Two, R3 -> false
    | R3, Onea -> false
    | Onea, R3 -> false
    | R3, Data -> false
    | Data, R3 -> false
    | R3, Select -> false
    | Select, R3 -> false
    | R3, Enable -> false
    | Enable, R3 -> false
    | R3, Bus2 -> false
    | Bus2, R3 -> false
    | R3, Bus1 -> false
    | Bus1, R3 -> false
    | R3, Bus0 -> false
    | Bus0, R3 -> false
    | R3, Bus_out -> false
    | Bus_out, R3 -> false
    | R3, Inb -> false
    | Inb, R3 -> false
    | R3, Ina -> false
    | Ina, R3 -> false
    | R3, Carry_in -> false
    | Carry_in, R3 -> false
    | R3, Carry_out -> false
    | Carry_out, R3 -> false
    | R3, Sum_out -> false
    | Sum_out, R3 -> false
    | R3, W4 -> false
    | W4, R3 -> false
    | R3, W3 -> false
    | W3, R3 -> false
    | R3, W2 -> false
    | W2, R3 -> false
    | R3, W1 -> false
    | W1, R3 -> false
    | R3, R5 -> false
    | R5, R3 -> false
    | R3, R4 -> false
    | R4, R3 -> false
    | R2, S -> false
    | S, R2 -> false
    | R2, R -> false
    | R, R2 -> false
    | R2, Qa -> false
    | Qa, R2 -> false
    | R2, Q -> false
    | Q, R2 -> false
    | R2, Yi -> false
    | Yi, R2 -> false
    | R2, Xi -> false
    | Xi, R2 -> false
    | R2, O2 -> false
    | O2, R2 -> false
    | R2, I2 -> false
    | I2, R2 -> false
    | R2, W1a -> false
    | W1a, R2 -> false
    | R2, O1a -> false
    | O1a, R2 -> false
    | R2, I1a -> false
    | I1a, R2 -> false
    | R2, Four -> false
    | Four, R2 -> false
    | R2, Three -> false
    | Three, R2 -> false
    | R2, Two -> false
    | Two, R2 -> false
    | R2, Onea -> false
    | Onea, R2 -> false
    | R2, Data -> false
    | Data, R2 -> false
    | R2, Select -> false
    | Select, R2 -> false
    | R2, Enable -> false
    | Enable, R2 -> false
    | R2, Bus2 -> false
    | Bus2, R2 -> false
    | R2, Bus1 -> false
    | Bus1, R2 -> false
    | R2, Bus0 -> false
    | Bus0, R2 -> false
    | R2, Bus_out -> false
    | Bus_out, R2 -> false
    | R2, Inb -> false
    | Inb, R2 -> false
    | R2, Ina -> false
    | Ina, R2 -> false
    | R2, Carry_in -> false
    | Carry_in, R2 -> false
    | R2, Carry_out -> false
    | Carry_out, R2 -> false
    | R2, Sum_out -> false
    | Sum_out, R2 -> false
    | R2, W4 -> false
    | W4, R2 -> false
    | R2, W3 -> false
    | W3, R2 -> false
    | R2, W2 -> false
    | W2, R2 -> false
    | R2, W1 -> false
    | W1, R2 -> false
    | R2, R5 -> false
    | R5, R2 -> false
    | R2, R4 -> false
    | R4, R2 -> false
    | R2, R3 -> false
    | R3, R2 -> false
    | R1, S -> false
    | S, R1 -> false
    | R1, R -> false
    | R, R1 -> false
    | R1, Qa -> false
    | Qa, R1 -> false
    | R1, Q -> false
    | Q, R1 -> false
    | R1, Yi -> false
    | Yi, R1 -> false
    | R1, Xi -> false
    | Xi, R1 -> false
    | R1, O2 -> false
    | O2, R1 -> false
    | R1, I2 -> false
    | I2, R1 -> false
    | R1, W1a -> false
    | W1a, R1 -> false
    | R1, O1a -> false
    | O1a, R1 -> false
    | R1, I1a -> false
    | I1a, R1 -> false
    | R1, Four -> false
    | Four, R1 -> false
    | R1, Three -> false
    | Three, R1 -> false
    | R1, Two -> false
    | Two, R1 -> false
    | R1, Onea -> false
    | Onea, R1 -> false
    | R1, Data -> false
    | Data, R1 -> false
    | R1, Select -> false
    | Select, R1 -> false
    | R1, Enable -> false
    | Enable, R1 -> false
    | R1, Bus2 -> false
    | Bus2, R1 -> false
    | R1, Bus1 -> false
    | Bus1, R1 -> false
    | R1, Bus0 -> false
    | Bus0, R1 -> false
    | R1, Bus_out -> false
    | Bus_out, R1 -> false
    | R1, Inb -> false
    | Inb, R1 -> false
    | R1, Ina -> false
    | Ina, R1 -> false
    | R1, Carry_in -> false
    | Carry_in, R1 -> false
    | R1, Carry_out -> false
    | Carry_out, R1 -> false
    | R1, Sum_out -> false
    | Sum_out, R1 -> false
    | R1, W4 -> false
    | W4, R1 -> false
    | R1, W3 -> false
    | W3, R1 -> false
    | R1, W2 -> false
    | W2, R1 -> false
    | R1, W1 -> false
    | W1, R1 -> false
    | R1, R5 -> false
    | R5, R1 -> false
    | R1, R4 -> false
    | R4, R1 -> false
    | R1, R3 -> false
    | R3, R1 -> false
    | R1, R2 -> false
    | R2, R1 -> false
    | O1, S -> false
    | S, O1 -> false
    | O1, R -> false
    | R, O1 -> false
    | O1, Qa -> false
    | Qa, O1 -> false
    | O1, Q -> false
    | Q, O1 -> false
    | O1, Yi -> false
    | Yi, O1 -> false
    | O1, Xi -> false
    | Xi, O1 -> false
    | O1, O2 -> false
    | O2, O1 -> false
    | O1, I2 -> false
    | I2, O1 -> false
    | O1, W1a -> false
    | W1a, O1 -> false
    | O1, O1a -> false
    | O1a, O1 -> false
    | O1, I1a -> false
    | I1a, O1 -> false
    | O1, Four -> false
    | Four, O1 -> false
    | O1, Three -> false
    | Three, O1 -> false
    | O1, Two -> false
    | Two, O1 -> false
    | O1, Onea -> false
    | Onea, O1 -> false
    | O1, Data -> false
    | Data, O1 -> false
    | O1, Select -> false
    | Select, O1 -> false
    | O1, Enable -> false
    | Enable, O1 -> false
    | O1, Bus2 -> false
    | Bus2, O1 -> false
    | O1, Bus1 -> false
    | Bus1, O1 -> false
    | O1, Bus0 -> false
    | Bus0, O1 -> false
    | O1, Bus_out -> false
    | Bus_out, O1 -> false
    | O1, Inb -> false
    | Inb, O1 -> false
    | O1, Ina -> false
    | Ina, O1 -> false
    | O1, Carry_in -> false
    | Carry_in, O1 -> false
    | O1, Carry_out -> false
    | Carry_out, O1 -> false
    | O1, Sum_out -> false
    | Sum_out, O1 -> false
    | O1, W4 -> false
    | W4, O1 -> false
    | O1, W3 -> false
    | W3, O1 -> false
    | O1, W2 -> false
    | W2, O1 -> false
    | O1, W1 -> false
    | W1, O1 -> false
    | O1, R5 -> false
    | R5, O1 -> false
    | O1, R4 -> false
    | R4, O1 -> false
    | O1, R3 -> false
    | R3, O1 -> false
    | O1, R2 -> false
    | R2, O1 -> false
    | O1, R1 -> false
    | R1, O1 -> false
    | I1, S -> false
    | S, I1 -> false
    | I1, R -> false
    | R, I1 -> false
    | I1, Qa -> false
    | Qa, I1 -> false
    | I1, Q -> false
    | Q, I1 -> false
    | I1, Yi -> false
    | Yi, I1 -> false
    | I1, Xi -> false
    | Xi, I1 -> false
    | I1, O2 -> false
    | O2, I1 -> false
    | I1, I2 -> false
    | I2, I1 -> false
    | I1, W1a -> false
    | W1a, I1 -> false
    | I1, O1a -> false
    | O1a, I1 -> false
    | I1, I1a -> false
    | I1a, I1 -> false
    | I1, Four -> false
    | Four, I1 -> false
    | I1, Three -> false
    | Three, I1 -> false
    | I1, Two -> false
    | Two, I1 -> false
    | I1, Onea -> false
    | Onea, I1 -> false
    | I1, Data -> false
    | Data, I1 -> false
    | I1, Select -> false
    | Select, I1 -> false
    | I1, Enable -> false
    | Enable, I1 -> false
    | I1, Bus2 -> false
    | Bus2, I1 -> false
    | I1, Bus1 -> false
    | Bus1, I1 -> false
    | I1, Bus0 -> false
    | Bus0, I1 -> false
    | I1, Bus_out -> false
    | Bus_out, I1 -> false
    | I1, Inb -> false
    | Inb, I1 -> false
    | I1, Ina -> false
    | Ina, I1 -> false
    | I1, Carry_in -> false
    | Carry_in, I1 -> false
    | I1, Carry_out -> false
    | Carry_out, I1 -> false
    | I1, Sum_out -> false
    | Sum_out, I1 -> false
    | I1, W4 -> false
    | W4, I1 -> false
    | I1, W3 -> false
    | W3, I1 -> false
    | I1, W2 -> false
    | W2, I1 -> false
    | I1, W1 -> false
    | W1, I1 -> false
    | I1, R5 -> false
    | R5, I1 -> false
    | I1, R4 -> false
    | R4, I1 -> false
    | I1, R3 -> false
    | R3, I1 -> false
    | I1, R2 -> false
    | R2, I1 -> false
    | I1, R1 -> false
    | R1, I1 -> false
    | I1, O1 -> false
    | O1, I1 -> false
    | CLK, S -> false
    | S, CLK -> false
    | CLK, R -> false
    | R, CLK -> false
    | CLK, Qa -> false
    | Qa, CLK -> false
    | CLK, Q -> false
    | Q, CLK -> false
    | CLK, Yi -> false
    | Yi, CLK -> false
    | CLK, Xi -> false
    | Xi, CLK -> false
    | CLK, O2 -> false
    | O2, CLK -> false
    | CLK, I2 -> false
    | I2, CLK -> false
    | CLK, W1a -> false
    | W1a, CLK -> false
    | CLK, O1a -> false
    | O1a, CLK -> false
    | CLK, I1a -> false
    | I1a, CLK -> false
    | CLK, Four -> false
    | Four, CLK -> false
    | CLK, Three -> false
    | Three, CLK -> false
    | CLK, Two -> false
    | Two, CLK -> false
    | CLK, Onea -> false
    | Onea, CLK -> false
    | CLK, Data -> false
    | Data, CLK -> false
    | CLK, Select -> false
    | Select, CLK -> false
    | CLK, Enable -> false
    | Enable, CLK -> false
    | CLK, Bus2 -> false
    | Bus2, CLK -> false
    | CLK, Bus1 -> false
    | Bus1, CLK -> false
    | CLK, Bus0 -> false
    | Bus0, CLK -> false
    | CLK, Bus_out -> false
    | Bus_out, CLK -> false
    | CLK, Inb -> false
    | Inb, CLK -> false
    | CLK, Ina -> false
    | Ina, CLK -> false
    | CLK, Carry_in -> false
    | Carry_in, CLK -> false
    | CLK, Carry_out -> false
    | Carry_out, CLK -> false
    | CLK, Sum_out -> false
    | Sum_out, CLK -> false
    | CLK, W4 -> false
    | W4, CLK -> false
    | CLK, W3 -> false
    | W3, CLK -> false
    | CLK, W2 -> false
    | W2, CLK -> false
    | CLK, W1 -> false
    | W1, CLK -> false
    | CLK, R5 -> false
    | R5, CLK -> false
    | CLK, R4 -> false
    | R4, CLK -> false
    | CLK, R3 -> false
    | R3, CLK -> false
    | CLK, R2 -> false
    | R2, CLK -> false
    | CLK, R1 -> false
    | R1, CLK -> false
    | CLK, O1 -> false
    | O1, CLK -> false
    | CLK, I1 -> false
    | I1, CLK -> false
    | Z, S -> false
    | S, Z -> false
    | Z, R -> false
    | R, Z -> false
    | Z, Qa -> false
    | Qa, Z -> false
    | Z, Q -> false
    | Q, Z -> false
    | Z, Yi -> false
    | Yi, Z -> false
    | Z, Xi -> false
    | Xi, Z -> false
    | Z, O2 -> false
    | O2, Z -> false
    | Z, I2 -> false
    | I2, Z -> false
    | Z, W1a -> false
    | W1a, Z -> false
    | Z, O1a -> false
    | O1a, Z -> false
    | Z, I1a -> false
    | I1a, Z -> false
    | Z, Four -> false
    | Four, Z -> false
    | Z, Three -> false
    | Three, Z -> false
    | Z, Two -> false
    | Two, Z -> false
    | Z, Onea -> false
    | Onea, Z -> false
    | Z, Data -> false
    | Data, Z -> false
    | Z, Select -> false
    | Select, Z -> false
    | Z, Enable -> false
    | Enable, Z -> false
    | Z, Bus2 -> false
    | Bus2, Z -> false
    | Z, Bus1 -> false
    | Bus1, Z -> false
    | Z, Bus0 -> false
    | Bus0, Z -> false
    | Z, Bus_out -> false
    | Bus_out, Z -> false
    | Z, Inb -> false
    | Inb, Z -> false
    | Z, Ina -> false
    | Ina, Z -> false
    | Z, Carry_in -> false
    | Carry_in, Z -> false
    | Z, Carry_out -> false
    | Carry_out, Z -> false
    | Z, Sum_out -> false
    | Sum_out, Z -> false
    | Z, W4 -> false
    | W4, Z -> false
    | Z, W3 -> false
    | W3, Z -> false
    | Z, W2 -> false
    | W2, Z -> false
    | Z, W1 -> false
    | W1, Z -> false
    | Z, R5 -> false
    | R5, Z -> false
    | Z, R4 -> false
    | R4, Z -> false
    | Z, R3 -> false
    | R3, Z -> false
    | Z, R2 -> false
    | R2, Z -> false
    | Z, R1 -> false
    | R1, Z -> false
    | Z, O1 -> false
    | O1, Z -> false
    | Z, I1 -> false
    | I1, Z -> false
    | Z, CLK -> false
    | CLK, Z -> false
    | Y, S -> false
    | S, Y -> false
    | Y, R -> false
    | R, Y -> false
    | Y, Qa -> false
    | Qa, Y -> false
    | Y, Q -> false
    | Q, Y -> false
    | Y, Yi -> false
    | Yi, Y -> false
    | Y, Xi -> false
    | Xi, Y -> false
    | Y, O2 -> false
    | O2, Y -> false
    | Y, I2 -> false
    | I2, Y -> false
    | Y, W1a -> false
    | W1a, Y -> false
    | Y, O1a -> false
    | O1a, Y -> false
    | Y, I1a -> false
    | I1a, Y -> false
    | Y, Four -> false
    | Four, Y -> false
    | Y, Three -> false
    | Three, Y -> false
    | Y, Two -> false
    | Two, Y -> false
    | Y, Onea -> false
    | Onea, Y -> false
    | Y, Data -> false
    | Data, Y -> false
    | Y, Select -> false
    | Select, Y -> false
    | Y, Enable -> false
    | Enable, Y -> false
    | Y, Bus2 -> false
    | Bus2, Y -> false
    | Y, Bus1 -> false
    | Bus1, Y -> false
    | Y, Bus0 -> false
    | Bus0, Y -> false
    | Y, Bus_out -> false
    | Bus_out, Y -> false
    | Y, Inb -> false
    | Inb, Y -> false
    | Y, Ina -> false
    | Ina, Y -> false
    | Y, Carry_in -> false
    | Carry_in, Y -> false
    | Y, Carry_out -> false
    | Carry_out, Y -> false
    | Y, Sum_out -> false
    | Sum_out, Y -> false
    | Y, W4 -> false
    | W4, Y -> false
    | Y, W3 -> false
    | W3, Y -> false
    | Y, W2 -> false
    | W2, Y -> false
    | Y, W1 -> false
    | W1, Y -> false
    | Y, R5 -> false
    | R5, Y -> false
    | Y, R4 -> false
    | R4, Y -> false
    | Y, R3 -> false
    | R3, Y -> false
    | Y, R2 -> false
    | R2, Y -> false
    | Y, R1 -> false
    | R1, Y -> false
    | Y, O1 -> false
    | O1, Y -> false
    | Y, I1 -> false
    | I1, Y -> false
    | Y, CLK -> false
    | CLK, Y -> false
    | Y, Z -> false
    | Z, Y -> false
    | X, S -> false
    | S, X -> false
    | X, R -> false
    | R, X -> false
    | X, Qa -> false
    | Qa, X -> false
    | X, Q -> false
    | Q, X -> false
    | X, Yi -> false
    | Yi, X -> false
    | X, Xi -> false
    | Xi, X -> false
    | X, O2 -> false
    | O2, X -> false
    | X, I2 -> false
    | I2, X -> false
    | X, W1a -> false
    | W1a, X -> false
    | X, O1a -> false
    | O1a, X -> false
    | X, I1a -> false
    | I1a, X -> false
    | X, Four -> false
    | Four, X -> false
    | X, Three -> false
    | Three, X -> false
    | X, Two -> false
    | Two, X -> false
    | X, Onea -> false
    | Onea, X -> false
    | X, Data -> false
    | Data, X -> false
    | X, Select -> false
    | Select, X -> false
    | X, Enable -> false
    | Enable, X -> false
    | X, Bus2 -> false
    | Bus2, X -> false
    | X, Bus1 -> false
    | Bus1, X -> false
    | X, Bus0 -> false
    | Bus0, X -> false
    | X, Bus_out -> false
    | Bus_out, X -> false
    | X, Inb -> false
    | Inb, X -> false
    | X, Ina -> false
    | Ina, X -> false
    | X, Carry_in -> false
    | Carry_in, X -> false
    | X, Carry_out -> false
    | Carry_out, X -> false
    | X, Sum_out -> false
    | Sum_out, X -> false
    | X, W4 -> false
    | W4, X -> false
    | X, W3 -> false
    | W3, X -> false
    | X, W2 -> false
    | W2, X -> false
    | X, W1 -> false
    | W1, X -> false
    | X, R5 -> false
    | R5, X -> false
    | X, R4 -> false
    | R4, X -> false
    | X, R3 -> false
    | R3, X -> false
    | X, R2 -> false
    | R2, X -> false
    | X, R1 -> false
    | R1, X -> false
    | X, O1 -> false
    | O1, X -> false
    | X, I1 -> false
    | I1, X -> false
    | X, CLK -> false
    | CLK, X -> false
    | X, Z -> false
    | Z, X -> false
    | X, Y -> false
    | Y, X -> false
    | S, S -> true
    | R, R -> true
    | Qa, Qa -> true
    | Q, Q -> true
    | Yi, Yi -> true
    | Xi, Xi -> true
    | O2, O2 -> true
    | I2, I2 -> true
    | W1a, W1a -> true
    | O1a, O1a -> true
    | I1a, I1a -> true
    | Four, Four -> true
    | Three, Three -> true
    | Two, Two -> true
    | Onea, Onea -> true
    | Data, Data -> true
    | Select, Select -> true
    | Enable, Enable -> true
    | Bus2, Bus2 -> true
    | Bus1, Bus1 -> true
    | Bus0, Bus0 -> true
    | Bus_out, Bus_out -> true
    | Inb, Inb -> true
    | Ina, Ina -> true
    | Carry_in, Carry_in -> true
    | Carry_out, Carry_out -> true
    | Sum_out, Sum_out -> true
    | W4, W4 -> true
    | W3, W3 -> true
    | W2, W2 -> true
    | W1, W1 -> true
    | R5, R5 -> true
    | R4, R4 -> true
    | R3, R3 -> true
    | R2, R2 -> true
    | R1, R1 -> true
    | O1, O1 -> true
    | I1, I1 -> true
    | CLK, CLK -> true
    | Z, Z -> true
    | Y, Y -> true
    | X, X -> true;;

type exp = Exp_name of name | Exp_bv of (int * nat) | Exp_uop of uop * exp |
  Exp_bop of exp * bop * exp | Exp_lop of exp * lop * exp |
  Exp_cop of exp * exp * exp | Exp_rsn of exp * nat | Exp_lsn of exp * nat |
  Exp_bitslice of name * nat * nat | Exp_bitsel of name * nat |
  Exp_index of name * exp;;

let rec equal_expa
  x0 x1 = match x0, x1 with
    Exp_bitsel (x101, x102), Exp_index (x111, x112) -> false
    | Exp_index (x111, x112), Exp_bitsel (x101, x102) -> false
    | Exp_bitslice (x91, x92, x93), Exp_index (x111, x112) -> false
    | Exp_index (x111, x112), Exp_bitslice (x91, x92, x93) -> false
    | Exp_bitslice (x91, x92, x93), Exp_bitsel (x101, x102) -> false
    | Exp_bitsel (x101, x102), Exp_bitslice (x91, x92, x93) -> false
    | Exp_lsn (x81, x82), Exp_index (x111, x112) -> false
    | Exp_index (x111, x112), Exp_lsn (x81, x82) -> false
    | Exp_lsn (x81, x82), Exp_bitsel (x101, x102) -> false
    | Exp_bitsel (x101, x102), Exp_lsn (x81, x82) -> false
    | Exp_lsn (x81, x82), Exp_bitslice (x91, x92, x93) -> false
    | Exp_bitslice (x91, x92, x93), Exp_lsn (x81, x82) -> false
    | Exp_rsn (x71, x72), Exp_index (x111, x112) -> false
    | Exp_index (x111, x112), Exp_rsn (x71, x72) -> false
    | Exp_rsn (x71, x72), Exp_bitsel (x101, x102) -> false
    | Exp_bitsel (x101, x102), Exp_rsn (x71, x72) -> false
    | Exp_rsn (x71, x72), Exp_bitslice (x91, x92, x93) -> false
    | Exp_bitslice (x91, x92, x93), Exp_rsn (x71, x72) -> false
    | Exp_rsn (x71, x72), Exp_lsn (x81, x82) -> false
    | Exp_lsn (x81, x82), Exp_rsn (x71, x72) -> false
    | Exp_cop (x61, x62, x63), Exp_index (x111, x112) -> false
    | Exp_index (x111, x112), Exp_cop (x61, x62, x63) -> false
    | Exp_cop (x61, x62, x63), Exp_bitsel (x101, x102) -> false
    | Exp_bitsel (x101, x102), Exp_cop (x61, x62, x63) -> false
    | Exp_cop (x61, x62, x63), Exp_bitslice (x91, x92, x93) -> false
    | Exp_bitslice (x91, x92, x93), Exp_cop (x61, x62, x63) -> false
    | Exp_cop (x61, x62, x63), Exp_lsn (x81, x82) -> false
    | Exp_lsn (x81, x82), Exp_cop (x61, x62, x63) -> false
    | Exp_cop (x61, x62, x63), Exp_rsn (x71, x72) -> false
    | Exp_rsn (x71, x72), Exp_cop (x61, x62, x63) -> false
    | Exp_lop (x51, x52, x53), Exp_index (x111, x112) -> false
    | Exp_index (x111, x112), Exp_lop (x51, x52, x53) -> false
    | Exp_lop (x51, x52, x53), Exp_bitsel (x101, x102) -> false
    | Exp_bitsel (x101, x102), Exp_lop (x51, x52, x53) -> false
    | Exp_lop (x51, x52, x53), Exp_bitslice (x91, x92, x93) -> false
    | Exp_bitslice (x91, x92, x93), Exp_lop (x51, x52, x53) -> false
    | Exp_lop (x51, x52, x53), Exp_lsn (x81, x82) -> false
    | Exp_lsn (x81, x82), Exp_lop (x51, x52, x53) -> false
    | Exp_lop (x51, x52, x53), Exp_rsn (x71, x72) -> false
    | Exp_rsn (x71, x72), Exp_lop (x51, x52, x53) -> false
    | Exp_lop (x51, x52, x53), Exp_cop (x61, x62, x63) -> false
    | Exp_cop (x61, x62, x63), Exp_lop (x51, x52, x53) -> false
    | Exp_bop (x41, x42, x43), Exp_index (x111, x112) -> false
    | Exp_index (x111, x112), Exp_bop (x41, x42, x43) -> false
    | Exp_bop (x41, x42, x43), Exp_bitsel (x101, x102) -> false
    | Exp_bitsel (x101, x102), Exp_bop (x41, x42, x43) -> false
    | Exp_bop (x41, x42, x43), Exp_bitslice (x91, x92, x93) -> false
    | Exp_bitslice (x91, x92, x93), Exp_bop (x41, x42, x43) -> false
    | Exp_bop (x41, x42, x43), Exp_lsn (x81, x82) -> false
    | Exp_lsn (x81, x82), Exp_bop (x41, x42, x43) -> false
    | Exp_bop (x41, x42, x43), Exp_rsn (x71, x72) -> false
    | Exp_rsn (x71, x72), Exp_bop (x41, x42, x43) -> false
    | Exp_bop (x41, x42, x43), Exp_cop (x61, x62, x63) -> false
    | Exp_cop (x61, x62, x63), Exp_bop (x41, x42, x43) -> false
    | Exp_bop (x41, x42, x43), Exp_lop (x51, x52, x53) -> false
    | Exp_lop (x51, x52, x53), Exp_bop (x41, x42, x43) -> false
    | Exp_uop (x31, x32), Exp_index (x111, x112) -> false
    | Exp_index (x111, x112), Exp_uop (x31, x32) -> false
    | Exp_uop (x31, x32), Exp_bitsel (x101, x102) -> false
    | Exp_bitsel (x101, x102), Exp_uop (x31, x32) -> false
    | Exp_uop (x31, x32), Exp_bitslice (x91, x92, x93) -> false
    | Exp_bitslice (x91, x92, x93), Exp_uop (x31, x32) -> false
    | Exp_uop (x31, x32), Exp_lsn (x81, x82) -> false
    | Exp_lsn (x81, x82), Exp_uop (x31, x32) -> false
    | Exp_uop (x31, x32), Exp_rsn (x71, x72) -> false
    | Exp_rsn (x71, x72), Exp_uop (x31, x32) -> false
    | Exp_uop (x31, x32), Exp_cop (x61, x62, x63) -> false
    | Exp_cop (x61, x62, x63), Exp_uop (x31, x32) -> false
    | Exp_uop (x31, x32), Exp_lop (x51, x52, x53) -> false
    | Exp_lop (x51, x52, x53), Exp_uop (x31, x32) -> false
    | Exp_uop (x31, x32), Exp_bop (x41, x42, x43) -> false
    | Exp_bop (x41, x42, x43), Exp_uop (x31, x32) -> false
    | Exp_bv x2, Exp_index (x111, x112) -> false
    | Exp_index (x111, x112), Exp_bv x2 -> false
    | Exp_bv x2, Exp_bitsel (x101, x102) -> false
    | Exp_bitsel (x101, x102), Exp_bv x2 -> false
    | Exp_bv x2, Exp_bitslice (x91, x92, x93) -> false
    | Exp_bitslice (x91, x92, x93), Exp_bv x2 -> false
    | Exp_bv x2, Exp_lsn (x81, x82) -> false
    | Exp_lsn (x81, x82), Exp_bv x2 -> false
    | Exp_bv x2, Exp_rsn (x71, x72) -> false
    | Exp_rsn (x71, x72), Exp_bv x2 -> false
    | Exp_bv x2, Exp_cop (x61, x62, x63) -> false
    | Exp_cop (x61, x62, x63), Exp_bv x2 -> false
    | Exp_bv x2, Exp_lop (x51, x52, x53) -> false
    | Exp_lop (x51, x52, x53), Exp_bv x2 -> false
    | Exp_bv x2, Exp_bop (x41, x42, x43) -> false
    | Exp_bop (x41, x42, x43), Exp_bv x2 -> false
    | Exp_bv x2, Exp_uop (x31, x32) -> false
    | Exp_uop (x31, x32), Exp_bv x2 -> false
    | Exp_name x1, Exp_index (x111, x112) -> false
    | Exp_index (x111, x112), Exp_name x1 -> false
    | Exp_name x1, Exp_bitsel (x101, x102) -> false
    | Exp_bitsel (x101, x102), Exp_name x1 -> false
    | Exp_name x1, Exp_bitslice (x91, x92, x93) -> false
    | Exp_bitslice (x91, x92, x93), Exp_name x1 -> false
    | Exp_name x1, Exp_lsn (x81, x82) -> false
    | Exp_lsn (x81, x82), Exp_name x1 -> false
    | Exp_name x1, Exp_rsn (x71, x72) -> false
    | Exp_rsn (x71, x72), Exp_name x1 -> false
    | Exp_name x1, Exp_cop (x61, x62, x63) -> false
    | Exp_cop (x61, x62, x63), Exp_name x1 -> false
    | Exp_name x1, Exp_lop (x51, x52, x53) -> false
    | Exp_lop (x51, x52, x53), Exp_name x1 -> false
    | Exp_name x1, Exp_bop (x41, x42, x43) -> false
    | Exp_bop (x41, x42, x43), Exp_name x1 -> false
    | Exp_name x1, Exp_uop (x31, x32) -> false
    | Exp_uop (x31, x32), Exp_name x1 -> false
    | Exp_name x1, Exp_bv x2 -> false
    | Exp_bv x2, Exp_name x1 -> false
    | Exp_index (x111, x112), Exp_index (y111, y112) ->
        equal_namea x111 y111 && equal_expa x112 y112
    | Exp_bitsel (x101, x102), Exp_bitsel (y101, y102) ->
        equal_namea x101 y101 && equal_nata x102 y102
    | Exp_bitslice (x91, x92, x93), Exp_bitslice (y91, y92, y93) ->
        equal_namea x91 y91 && (equal_nata x92 y92 && equal_nata x93 y93)
    | Exp_lsn (x81, x82), Exp_lsn (y81, y82) ->
        equal_expa x81 y81 && equal_nata x82 y82
    | Exp_rsn (x71, x72), Exp_rsn (y71, y72) ->
        equal_expa x71 y71 && equal_nata x72 y72
    | Exp_cop (x61, x62, x63), Exp_cop (y61, y62, y63) ->
        equal_expa x61 y61 && (equal_expa x62 y62 && equal_expa x63 y63)
    | Exp_lop (x51, x52, x53), Exp_lop (y51, y52, y53) ->
        equal_expa x51 y51 && (equal_lop x52 y52 && equal_expa x53 y53)
    | Exp_bop (x41, x42, x43), Exp_bop (y41, y42, y43) ->
        equal_expa x41 y41 && (equal_bop x42 y42 && equal_expa x43 y43)
    | Exp_uop (x31, x32), Exp_uop (y31, y32) ->
        equal_uop x31 y31 && equal_expa x32 y32
    | Exp_bv x2, Exp_bv y2 -> equal_proda equal_int equal_nat x2 y2
    | Exp_name x1, Exp_name y1 -> equal_namea x1 y1;;

let equal_exp = ({equal = equal_expa} : exp equal);;

let equal_name = ({equal = equal_namea} : name equal);;

let rec equal_option _A
  x0 x1 = match x0, x1 with None, Some x2 -> false
    | Some x2, None -> false
    | Some x2, Some y2 -> eq _A x2 y2
    | None, None -> true;;

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

type sensit = Trg_star | Trg_posed of exp | Trg_neged of exp | Trg_exp of exp;;

type statement = Stm_skip | Stm_finish | Stm_disab of name |
  Stm_dba of exp list * int * exp | Stm_tba of exp list * sensit list * exp |
  Stm_dnba of exp list * int * exp | Stm_tnba of exp list * sensit list * exp |
  Stm_ife of exp * statement * statement | Stm_while of exp * statement |
  Stm_cb of name option * statement |
  Stm_case of exp * (exp * statement) list * statement |
  Stm_sensl of sensit list * statement | Stm_delay of nat * statement |
  Stm_seq of statement * statement;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let rec equal_sensita
  x0 x1 = match x0, x1 with Trg_neged x3, Trg_exp x4 -> false
    | Trg_exp x4, Trg_neged x3 -> false
    | Trg_posed x2, Trg_exp x4 -> false
    | Trg_exp x4, Trg_posed x2 -> false
    | Trg_posed x2, Trg_neged x3 -> false
    | Trg_neged x3, Trg_posed x2 -> false
    | Trg_star, Trg_exp x4 -> false
    | Trg_exp x4, Trg_star -> false
    | Trg_star, Trg_neged x3 -> false
    | Trg_neged x3, Trg_star -> false
    | Trg_star, Trg_posed x2 -> false
    | Trg_posed x2, Trg_star -> false
    | Trg_exp x4, Trg_exp y4 -> equal_expa x4 y4
    | Trg_neged x3, Trg_neged y3 -> equal_expa x3 y3
    | Trg_posed x2, Trg_posed y2 -> equal_expa x2 y2
    | Trg_star, Trg_star -> true;;

let equal_sensit = ({equal = equal_sensita} : sensit equal);;

let rec equal_statementa
  x0 x1 = match x0, x1 with
    Stm_delay (x131, x132), Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_delay (x131, x132) -> false
    | Stm_sensl (x121, x122), Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_sensl (x121, x122) -> false
    | Stm_case (x111, x112, x113), Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_case (x111, x112, x113) -> false
    | Stm_cb (x101, x102), Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_cb (x101, x102) -> false
    | Stm_while (x91, x92), Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_while (x91, x92) -> false
    | Stm_ife (x81, x82, x83), Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_ife (x81, x82, x83) -> false
    | Stm_tnba (x71, x72, x73), Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_tnba (x71, x72, x73) -> false
    | Stm_dnba (x61, x62, x63), Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_dnba (x61, x62, x63) -> false
    | Stm_tba (x51, x52, x53), Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_tba (x51, x52, x53) -> false
    | Stm_dba (x41, x42, x43), Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_dba (x41, x42, x43) -> false
    | Stm_disab x3, Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_disab x3 -> false
    | Stm_disab x3, Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_disab x3 -> false
    | Stm_disab x3, Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_disab x3 -> false
    | Stm_disab x3, Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_disab x3 -> false
    | Stm_disab x3, Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_disab x3 -> false
    | Stm_disab x3, Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_disab x3 -> false
    | Stm_disab x3, Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_disab x3 -> false
    | Stm_disab x3, Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_disab x3 -> false
    | Stm_disab x3, Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_disab x3 -> false
    | Stm_disab x3, Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_disab x3 -> false
    | Stm_disab x3, Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_disab x3 -> false
    | Stm_finish, Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_finish -> false
    | Stm_finish, Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_finish -> false
    | Stm_finish, Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_finish -> false
    | Stm_finish, Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_finish -> false
    | Stm_finish, Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_finish -> false
    | Stm_finish, Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_finish -> false
    | Stm_finish, Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_finish -> false
    | Stm_finish, Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_finish -> false
    | Stm_finish, Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_finish -> false
    | Stm_finish, Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_finish -> false
    | Stm_finish, Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_finish -> false
    | Stm_finish, Stm_disab x3 -> false
    | Stm_disab x3, Stm_finish -> false
    | Stm_skip, Stm_seq (x141, x142) -> false
    | Stm_seq (x141, x142), Stm_skip -> false
    | Stm_skip, Stm_delay (x131, x132) -> false
    | Stm_delay (x131, x132), Stm_skip -> false
    | Stm_skip, Stm_sensl (x121, x122) -> false
    | Stm_sensl (x121, x122), Stm_skip -> false
    | Stm_skip, Stm_case (x111, x112, x113) -> false
    | Stm_case (x111, x112, x113), Stm_skip -> false
    | Stm_skip, Stm_cb (x101, x102) -> false
    | Stm_cb (x101, x102), Stm_skip -> false
    | Stm_skip, Stm_while (x91, x92) -> false
    | Stm_while (x91, x92), Stm_skip -> false
    | Stm_skip, Stm_ife (x81, x82, x83) -> false
    | Stm_ife (x81, x82, x83), Stm_skip -> false
    | Stm_skip, Stm_tnba (x71, x72, x73) -> false
    | Stm_tnba (x71, x72, x73), Stm_skip -> false
    | Stm_skip, Stm_dnba (x61, x62, x63) -> false
    | Stm_dnba (x61, x62, x63), Stm_skip -> false
    | Stm_skip, Stm_tba (x51, x52, x53) -> false
    | Stm_tba (x51, x52, x53), Stm_skip -> false
    | Stm_skip, Stm_dba (x41, x42, x43) -> false
    | Stm_dba (x41, x42, x43), Stm_skip -> false
    | Stm_skip, Stm_disab x3 -> false
    | Stm_disab x3, Stm_skip -> false
    | Stm_skip, Stm_finish -> false
    | Stm_finish, Stm_skip -> false
    | Stm_seq (x141, x142), Stm_seq (y141, y142) ->
        equal_statementa x141 y141 && equal_statementa x142 y142
    | Stm_delay (x131, x132), Stm_delay (y131, y132) ->
        equal_nata x131 y131 && equal_statementa x132 y132
    | Stm_sensl (x121, x122), Stm_sensl (y121, y122) ->
        equal_list equal_sensit x121 y121 && equal_statementa x122 y122
    | Stm_case (x111, x112, x113), Stm_case (y111, y112, y113) ->
        equal_expa x111 y111 &&
          (equal_list (equal_prod equal_exp (equal_statement ())) x112 y112 &&
            equal_statementa x113 y113)
    | Stm_cb (x101, x102), Stm_cb (y101, y102) ->
        equal_option equal_name x101 y101 && equal_statementa x102 y102
    | Stm_while (x91, x92), Stm_while (y91, y92) ->
        equal_expa x91 y91 && equal_statementa x92 y92
    | Stm_ife (x81, x82, x83), Stm_ife (y81, y82, y83) ->
        equal_expa x81 y81 &&
          (equal_statementa x82 y82 && equal_statementa x83 y83)
    | Stm_tnba (x71, x72, x73), Stm_tnba (y71, y72, y73) ->
        equal_list equal_exp x71 y71 &&
          (equal_list equal_sensit x72 y72 && equal_expa x73 y73)
    | Stm_dnba (x61, x62, x63), Stm_dnba (y61, y62, y63) ->
        equal_list equal_exp x61 y61 &&
          (equal_inta x62 y62 && equal_expa x63 y63)
    | Stm_tba (x51, x52, x53), Stm_tba (y51, y52, y53) ->
        equal_list equal_exp x51 y51 &&
          (equal_list equal_sensit x52 y52 && equal_expa x53 y53)
    | Stm_dba (x41, x42, x43), Stm_dba (y41, y42, y43) ->
        equal_list equal_exp x41 y41 &&
          (equal_inta x42 y42 && equal_expa x43 y43)
    | Stm_disab x3, Stm_disab y3 -> equal_namea x3 y3
    | Stm_finish, Stm_finish -> true
    | Stm_skip, Stm_skip -> true
and equal_statement () = ({equal = equal_statementa} : statement equal);;
let equal_statement = equal_statement ();;

type process = Cpt_stm of statement | Cpt_alw of sensit list * process |
  Cpt_dca of int * exp list * exp * exp;;

let rec equal_process
  x0 x1 = match x0, x1 with
    Cpt_alw (x21, x22), Cpt_dca (x31, x32, x33, x34) -> false
    | Cpt_dca (x31, x32, x33, x34), Cpt_alw (x21, x22) -> false
    | Cpt_stm x1, Cpt_dca (x31, x32, x33, x34) -> false
    | Cpt_dca (x31, x32, x33, x34), Cpt_stm x1 -> false
    | Cpt_stm x1, Cpt_alw (x21, x22) -> false
    | Cpt_alw (x21, x22), Cpt_stm x1 -> false
    | Cpt_dca (x31, x32, x33, x34), Cpt_dca (y31, y32, y33, y34) ->
        equal_inta x31 y31 &&
          (equal_list equal_exp x32 y32 &&
            (equal_expa x33 y33 && equal_expa x34 y34))
    | Cpt_alw (x21, x22), Cpt_alw (y21, y22) ->
        equal_list equal_sensit x21 y21 && equal_process x22 y22
    | Cpt_stm x1, Cpt_stm y1 -> equal_statementa x1 y1;;

type event = Evt_upd of exp * (int * nat) | Evt_updl of event list * process |
  Evt_inact of process | Evt_fut of nat * process |
  Evt_listn of sensit list * process;;

let rec equal_event () = ({equal = equal_eventa} : event equal)
and equal_eventa
  x0 x1 = match x0, x1 with Evt_fut (x41, x42), Evt_listn (x51, x52) -> false
    | Evt_listn (x51, x52), Evt_fut (x41, x42) -> false
    | Evt_inact x3, Evt_listn (x51, x52) -> false
    | Evt_listn (x51, x52), Evt_inact x3 -> false
    | Evt_inact x3, Evt_fut (x41, x42) -> false
    | Evt_fut (x41, x42), Evt_inact x3 -> false
    | Evt_updl (x21, x22), Evt_listn (x51, x52) -> false
    | Evt_listn (x51, x52), Evt_updl (x21, x22) -> false
    | Evt_updl (x21, x22), Evt_fut (x41, x42) -> false
    | Evt_fut (x41, x42), Evt_updl (x21, x22) -> false
    | Evt_updl (x21, x22), Evt_inact x3 -> false
    | Evt_inact x3, Evt_updl (x21, x22) -> false
    | Evt_upd (x11, x12), Evt_listn (x51, x52) -> false
    | Evt_listn (x51, x52), Evt_upd (x11, x12) -> false
    | Evt_upd (x11, x12), Evt_fut (x41, x42) -> false
    | Evt_fut (x41, x42), Evt_upd (x11, x12) -> false
    | Evt_upd (x11, x12), Evt_inact x3 -> false
    | Evt_inact x3, Evt_upd (x11, x12) -> false
    | Evt_upd (x11, x12), Evt_updl (x21, x22) -> false
    | Evt_updl (x21, x22), Evt_upd (x11, x12) -> false
    | Evt_listn (x51, x52), Evt_listn (y51, y52) ->
        equal_list equal_sensit x51 y51 && equal_process x52 y52
    | Evt_fut (x41, x42), Evt_fut (y41, y42) ->
        equal_nata x41 y41 && equal_process x42 y42
    | Evt_inact x3, Evt_inact y3 -> equal_process x3 y3
    | Evt_updl (x21, x22), Evt_updl (y21, y22) ->
        equal_list (equal_event ()) x21 y21 && equal_process x22 y22
    | Evt_upd (x11, x12), Evt_upd (y11, y12) ->
        equal_expa x11 y11 && equal_proda equal_int equal_nat x12 y12;;
let equal_event = equal_event ();;

type 'a set = Set of 'a list | Coset of 'a list;;

type top = Top_in of nat * nat * name list | Top_out of nat * nat * name list |
  Top_io of nat * nat * name list | Top_wire of nat * nat * name list |
  Top_reg of nat * nat * name list | Top_assign of int * exp list * exp |
  Top_initial of statement | Top_always of statement;;

type program = Prog_mod of name list * top list;;

type 'a configuration_ext =
  Configuration_ext of
    (name * (int * nat)) list * nat * process list * event list * event list *
      event list * event list * event list * name set * bool * 'a;;

let rec plus_nat
  x0 n = match x0, n with Suc m, n -> plus_nat m (Suc n)
    | Zero_nat, n -> n;;

let one_nat : nat = Suc Zero_nat;;

let rec nat_of_num
  = function Bit1 n -> let m = nat_of_num n in
                       Suc (plus_nat m m)
    | Bit0 n -> let m = nat_of_num n in
                plus_nat m m
    | One -> one_nat;;

let rec nat
  = function Pos k -> nat_of_num k
    | Zero_int -> Zero_nat
    | Neg k -> Zero_nat;;

let rec comp f g = (fun x -> f (g x));;

let rec fold
  f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
    | f, [], s -> s;;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec membera _A
  x0 y = match x0, y with [], y -> false
    | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec inserta _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec insert _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (removeAll _A x xs)
    | x, Set xs -> Set (inserta _A x xs);;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec map
  f x1 = match f, x1 with f, [] -> []
    | f, x21 :: x22 -> f x21 :: map f x22;;

let rec awake
  n1 e =
    (match e with Evt_upd (_, _) -> false | Evt_updl (_, _) -> false
      | Evt_inact _ -> false | Evt_fut (n2, _) -> equal_nata n1 n2
      | Evt_listn (_, _) -> false);;

let rec cfg_listne_update
  cfg_listnea
    (Configuration_ext
      (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
        cfg_listne, cfg_disabs, cfg_finish, more))
    = Configuration_ext
        (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
          cfg_listnea cfg_listne, cfg_disabs, cfg_finish, more);;

let rec cfg_inacte_update
  cfg_inactea
    (Configuration_ext
      (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
        cfg_listne, cfg_disabs, cfg_finish, more))
    = Configuration_ext
        (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inactea cfg_inacte,
          cfg_nbaue, cfg_fute, cfg_listne, cfg_disabs, cfg_finish, more);;

let rec cfg_upde_update
  cfg_updea
    (Configuration_ext
      (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
        cfg_listne, cfg_disabs, cfg_finish, more))
    = Configuration_ext
        (cfg_env, cfg_time, cfg_actp, cfg_updea cfg_upde, cfg_inacte, cfg_nbaue,
          cfg_fute, cfg_listne, cfg_disabs, cfg_finish, more);;

let rec cfg_fute_update
  cfg_futea
    (Configuration_ext
      (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
        cfg_listne, cfg_disabs, cfg_finish, more))
    = Configuration_ext
        (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue,
          cfg_futea cfg_fute, cfg_listne, cfg_disabs, cfg_finish, more);;

let rec cfg_actp_update
  cfg_actpa
    (Configuration_ext
      (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
        cfg_listne, cfg_disabs, cfg_finish, more))
    = Configuration_ext
        (cfg_env, cfg_time, cfg_actpa cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue,
          cfg_fute, cfg_listne, cfg_disabs, cfg_finish, more);;

let rec cfg_env_update
  cfg_enva
    (Configuration_ext
      (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
        cfg_listne, cfg_disabs, cfg_finish, more))
    = Configuration_ext
        (cfg_enva cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue,
          cfg_fute, cfg_listne, cfg_disabs, cfg_finish, more);;

let rec senslexp
  e = (match e with Exp_name _ -> [Trg_exp e] | Exp_bv _ -> []
        | Exp_uop (_, a) -> senslexp a
        | Exp_bop (e1, _, e2) -> senslexp e1 @ senslexp e2
        | Exp_lop (e1, _, e2) -> senslexp e1 @ senslexp e2
        | Exp_cop (ea, te, fe) -> senslexp ea @ senslexp te @ senslexp fe
        | Exp_rsn (ea, _) -> senslexp ea | Exp_lsn (ea, _) -> senslexp ea
        | Exp_bitslice (_, _, _) -> [Trg_exp e]
        | Exp_bitsel (_, _) -> [Trg_exp e] | Exp_index (_, _) -> [Trg_exp e]);;

let rec toptoinact
  en x1 = match en, x1 with
    en, Top_assign (d, el, e) ->
      (if null (senslexp e) && equal_inta d Zero_int
        then [Evt_inact (Cpt_dca (Neg One, el, e, e))] else [])
    | en, Top_always (Stm_delay (Zero_nat, s)) -> [Evt_inact (Cpt_stm s)]
    | uu, Top_in (v, va, vb) -> []
    | uu, Top_out (v, va, vb) -> []
    | uu, Top_io (v, va, vb) -> []
    | uu, Top_wire (v, va, vb) -> []
    | uu, Top_reg (v, va, vb) -> []
    | uu, Top_initial v -> []
    | uu, Top_always Stm_skip -> []
    | uu, Top_always Stm_finish -> []
    | uu, Top_always (Stm_disab va) -> []
    | uu, Top_always (Stm_dba (va, vb, vc)) -> []
    | uu, Top_always (Stm_tba (va, vb, vc)) -> []
    | uu, Top_always (Stm_dnba (va, vb, vc)) -> []
    | uu, Top_always (Stm_tnba (va, vb, vc)) -> []
    | uu, Top_always (Stm_ife (va, vb, vc)) -> []
    | uu, Top_always (Stm_while (va, vb)) -> []
    | uu, Top_always (Stm_cb (va, vb)) -> []
    | uu, Top_always (Stm_case (va, vb, vc)) -> []
    | uu, Top_always (Stm_sensl (va, vb)) -> []
    | uu, Top_always (Stm_delay (Suc vc, vb)) -> []
    | uu, Top_always (Stm_seq (va, vb)) -> [];;

let rec minus_nat
  m n = match m, n with Suc m, Suc n -> minus_nat m n
    | Zero_nat, n -> Zero_nat
    | m, Zero_nat -> m;;

let rec addavar
  en x1 l = match en, x1, l with
    en, q :: nl, l -> [(q, (Zero_int, l))] @ addavar en nl l
    | en, [], l -> en;;

let rec updateenv
  en x1 = match en, x1 with
    en, Top_in (n2, n1, nl) ->
      addavar en nl (plus_nat (minus_nat n2 n1) one_nat)
    | en, Top_out (n2, n1, nl) ->
        addavar en nl (plus_nat (minus_nat n2 n1) one_nat)
    | en, Top_io (n2, n1, nl) ->
        addavar en nl (plus_nat (minus_nat n2 n1) one_nat)
    | en, Top_reg (n2, n1, nl) ->
        addavar en nl (plus_nat (minus_nat n2 n1) one_nat)
    | en, Top_wire (n2, n1, nl) ->
        addavar en nl (plus_nat (minus_nat n2 n1) one_nat)
    | en, Top_assign (v, va, vb) -> []
    | en, Top_initial v -> []
    | en, Top_always v -> [];;

let rec toptoproc
  = function Top_initial s -> Cpt_stm s
    | Top_in (v, va, vb) -> Cpt_stm Stm_skip
    | Top_out (v, va, vb) -> Cpt_stm Stm_skip
    | Top_io (v, va, vb) -> Cpt_stm Stm_skip
    | Top_wire (v, va, vb) -> Cpt_stm Stm_skip
    | Top_reg (v, va, vb) -> Cpt_stm Stm_skip
    | Top_assign (v, va, vb) -> Cpt_stm Stm_skip
    | Top_always v -> Cpt_stm Stm_skip;;

let bot_set : 'a set = Set [];;

let initconfig : unit configuration_ext
  = Configuration_ext
      ([], Zero_nat, [], [], [], [], [], [], bot_set, false, ());;

let rec timeof
  ev = (match ev with Evt_upd (_, _) -> Zero_nat | Evt_updl (_, _) -> Zero_nat
         | Evt_inact _ -> Zero_nat | Evt_fut (n, _) -> n
         | Evt_listn (_, _) -> Zero_nat);;

let rec addevent
  ev x1 = match ev, x1 with ev, [] -> [ev]
    | ev, x :: xs ->
        (if less_eq_nat (timeof ev) (timeof x) then ev :: x :: xs
          else x :: addevent ev xs);;

let rec toptofut
  uu x1 = match uu, x1 with uu, [] -> []
    | tm, Top_assign (d, el, e) :: tpl ->
        (if null (senslexp e) && less_int Zero_int d
          then addevent
                 (Evt_fut (plus_nat (nat d) tm, Cpt_dca (Neg One, el, e, e)))
                 (toptofut tm tpl)
          else toptofut tm tpl)
    | tm, Top_always (Stm_delay (Suc n, s)) :: tpl ->
        addevent (Evt_fut (plus_nat (Suc n) tm, Cpt_stm s)) (toptofut tm tpl)
    | tm, Top_in (v, va, vb) :: tpl -> toptofut tm tpl
    | tm, Top_out (v, va, vb) :: tpl -> toptofut tm tpl
    | tm, Top_io (v, va, vb) :: tpl -> toptofut tm tpl
    | tm, Top_wire (v, va, vb) :: tpl -> toptofut tm tpl
    | tm, Top_reg (v, va, vb) :: tpl -> toptofut tm tpl
    | tm, Top_initial v :: tpl -> toptofut tm tpl
    | tm, Top_always Stm_skip :: tpl -> toptofut tm tpl
    | tm, Top_always Stm_finish :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_disab va) :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_dba (va, vb, vc)) :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_tba (va, vb, vc)) :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_dnba (va, vb, vc)) :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_tnba (va, vb, vc)) :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_ife (va, vb, vc)) :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_while (va, vb)) :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_cb (va, vb)) :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_case (va, vb, vc)) :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_sensl (va, vb)) :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_delay (Zero_nat, vb)) :: tpl -> toptofut tm tpl
    | tm, Top_always (Stm_seq (va, vb)) :: tpl -> toptofut tm tpl;;

let rec senslstm
  s = (match s with Stm_skip -> [] | Stm_finish -> [] | Stm_disab _ -> []
        | Stm_dba (_, _, a) -> senslexp a | Stm_tba (_, _, a) -> senslexp a
        | Stm_dnba (_, _, a) -> senslexp a | Stm_tnba (_, _, a) -> senslexp a
        | Stm_ife (_, ts, fs) -> senslstm ts @ senslstm fs
        | Stm_while (_, a) -> senslstm a | Stm_cb (_, a) -> senslstm a
        | Stm_case (e, csl, ds) ->
          (match csl with [] -> senslstm ds
            | cs :: csla ->
              senslstm (snd cs) @ senslstm (Stm_case (e, csla, ds)))
        | Stm_sensl (_, a) -> senslstm a | Stm_delay (_, a) -> senslstm a
        | Stm_seq (s1, s2) -> senslstm s1 @ senslstm s2);;

let rec toptole
  tpl = (match tpl with [] -> [] | Top_in (_, _, _) :: tpla -> toptole tpla
          | Top_out (_, _, _) :: tpla -> toptole tpla
          | Top_io (_, _, _) :: tpla -> toptole tpla
          | Top_wire (_, _, _) :: tpla -> toptole tpla
          | Top_reg (_, _, _) :: tpla -> toptole tpla
          | Top_assign (d, el, e) :: tpla ->
            (match senslexp e with [] -> toptole tpla
              | s :: sl ->
                [Evt_listn (s :: sl, Cpt_dca (d, el, e, e))] @ toptole tpla)
          | Top_initial _ :: tpla -> toptole tpla
          | Top_always Stm_skip :: tpla -> toptole tpla
          | Top_always Stm_finish :: tpla -> toptole tpla
          | Top_always (Stm_disab _) :: tpla -> toptole tpla
          | Top_always (Stm_dba (_, _, _)) :: tpla -> toptole tpla
          | Top_always (Stm_tba (_, _, _)) :: tpla -> toptole tpla
          | Top_always (Stm_dnba (_, _, _)) :: tpla -> toptole tpla
          | Top_always (Stm_tnba (_, _, _)) :: tpla -> toptole tpla
          | Top_always (Stm_ife (_, _, _)) :: tpla -> toptole tpla
          | Top_always (Stm_while (_, _)) :: tpla -> toptole tpla
          | Top_always (Stm_cb (_, _)) :: tpla -> toptole tpla
          | Top_always (Stm_case (_, _, _)) :: tpla -> toptole tpla
          | Top_always (Stm_sensl (sl, s)) :: tpla ->
            let sla =
              (if equal_list equal_sensit sl [Trg_star] then senslstm s else sl)
              in
            [Evt_listn (sla, Cpt_stm s)] @ toptole tpla
          | Top_always (Stm_delay (_, _)) :: tpla -> toptole tpla
          | Top_always (Stm_seq (_, _)) :: tpla -> toptole tpla);;

let rec getbvenv
  q en =
    (match en with [] -> (Zero_int, Zero_nat)
      | p :: pl -> (if equal_namea (fst p) q then snd p else getbvenv q pl));;

let rec power
  one times a x3 = match one, times, a, x3 with
    one, times, a, Suc n -> times a (power one times a n)
    | one, times, a, Zero_nat -> one;;

let rec powera _A = power (one _A.one_power) (times _A.times_power);;

let rec shiftr_int x n = div_inta x (powera power_int (Pos (Bit0 One)) n);;

let rec bvrsn v1 n = (shiftr_int (fst v1) n, snd v1);;

let rec mkuevents
  en el bv =
    (match el with [] -> []
      | e :: ela ->
        (match e
          with Exp_name q ->
            Evt_upd (e, bv) :: mkuevents en ela (bvrsn bv (snd (getbvenv q en)))
          | Exp_bv _ -> mkuevents en ela bv
          | Exp_uop (_, _) -> mkuevents en ela bv
          | Exp_bop (_, _, _) -> mkuevents en ela bv
          | Exp_lop (_, _, _) -> mkuevents en ela bv
          | Exp_cop (_, _, _) -> mkuevents en ela bv
          | Exp_rsn (_, _) -> mkuevents en ela bv
          | Exp_lsn (_, _) -> mkuevents en ela bv
          | Exp_bitslice (_, n2, n1) ->
            Evt_upd (e, bv) ::
              mkuevents en ela (bvrsn bv (plus_nat (minus_nat n2 n1) one_nat))
          | Exp_bitsel (_, _) ->
            Evt_upd (e, bv) :: mkuevents en ela (bvrsn bv one_nat)
          | Exp_index (_, _) ->
            Evt_upd (e, bv) :: mkuevents en ela (bvrsn bv one_nat)));;

let rec bin_rest w = div_inta w (Pos (Bit0 One));;

let rec bin_last w = equal_inta (mod_int w (Pos (Bit0 One))) (Pos One);;

let rec bit k b = plus_inta (plus_inta (if b then Pos One else Zero_int) k) k;;

let rec bitAND_int
  x y = (if equal_inta x Zero_int then Zero_int
          else (if equal_inta x (Neg One) then y
                 else bit (bitAND_int (bin_rest x) (bin_rest y))
                        (bin_last x && bin_last y)));;

let rec maskn n = minus_inta (powera power_int (Pos (Bit0 One)) n) (Pos One);;

let rec slicebv
  bv n2 n1 =
    (bitAND_int (shiftr_int (fst bv) n1)
       (maskn (plus_nat (minus_nat n2 n1) one_nat)),
      plus_nat (minus_nat n2 n1) one_nat);;

let rec bitNOT_int x = (fun xa -> minus_inta (uminus_int xa) (Pos One)) x;;

let rec bitOR_int
  x = (fun xa y -> bitNOT_int (bitAND_int (bitNOT_int xa) (bitNOT_int y))) x;;

let rec bitXOR_int
  x = (fun xa y ->
        bitOR_int (bitAND_int xa (bitNOT_int y)) (bitAND_int (bitNOT_int xa) y))
        x;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec shiftl_int x n = times_inta x (powera power_int (Pos (Bit0 One)) n);;

let rec slicebva
  bv1 bv2 n2 n1 =
    (bitOR_int
       (bitAND_int (fst bv1)
         (bitNOT_int
           (shiftl_int (maskn (plus_nat (minus_nat n2 n1) one_nat)) n1)))
       (shiftl_int
         (bitAND_int (fst bv2) (maskn (plus_nat (minus_nat n2 n1) one_nat)))
         n1),
      snd bv1);;

let rec bvlsn v1 n = (shiftl_int (fst v1) n, snd v1);;

let rec concbv
  bv1 bv2 =
    let bv = bvlsn (fst bv1, plus_nat (snd bv1) (snd bv2)) (snd bv2) in
    slicebva bv bv2 (minus_nat (snd bv2) one_nat) Zero_nat;;

let rec binopbv
  v1 vop v2 =
    (match vop
      with BvsMULT -> (times_inta (fst v1) (fst v2), plus_nat (snd v1) (snd v2))
      | BvsPLUS -> (plus_inta (fst v1) (fst v2), max ord_nat (snd v1) (snd v2))
      | BvsSUB -> (minus_inta (fst v1) (fst v2), max ord_nat (snd v1) (snd v2))
      | BvsDIV -> (div_inta (fst v1) (fst v2), max ord_nat (snd v1) (snd v2))
      | BvsMOD -> (mod_int (fst v1) (fst v2), max ord_nat (snd v1) (snd v2))
      | BvsAND -> (bitAND_int (fst v1) (fst v2), max ord_nat (snd v1) (snd v2))
      | BvsOR -> (bitOR_int (fst v1) (fst v2), max ord_nat (snd v1) (snd v2))
      | BvsXOR -> (bitXOR_int (fst v1) (fst v2), max ord_nat (snd v1) (snd v2))
      | BvsXNOR ->
        (bitNOT_int (bitXOR_int (fst v1) (fst v2)),
          max ord_nat (snd v1) (snd v2))
      | BvsCONC -> concbv v1 v2);;

let rec unopbv
  vop v =
    (match vop
      with BvPOS ->
        (if less_int (fst v) Zero_int then (uminus_int (fst v), snd v) else v)
      | BvNEG -> (uminus_int (fst v), snd v)
      | BvNOT ->
        (if less_eq_int (Pos One) (fst v) then (Zero_int, snd v)
          else (Pos One, snd v))
      | BvCOMP -> (bitNOT_int (fst v), snd v));;

let rec booltobv b = (if b then (Pos One, one_nat) else (Zero_int, one_nat));;

let rec lopbv
  v1 vop v2 =
    (match vop with BvsLT -> booltobv (less_int (fst v1) (fst v2))
      | BvsLTE -> booltobv (less_eq_int (fst v1) (fst v2))
      | BvsGT -> booltobv (less_int (fst v2) (fst v1))
      | BvsGTE -> booltobv (less_eq_int (fst v2) (fst v1))
      | BvsEQ -> booltobv (equal_inta (fst v1) (fst v2))
      | BvsNEQ -> booltobv (not (equal_inta (fst v1) (fst v2)))
      | BvsLAND ->
        booltobv
          (less_eq_int (Pos One) (fst v1) && less_eq_int (Pos One) (fst v2))
      | BvsLOR ->
        booltobv
          (less_eq_int (Pos One) (fst v1) && less_eq_int (Pos One) (fst v2)));;

let rec evalexp
  en x1 = match en, x1 with en, Exp_name q -> getbvenv q en
    | en, Exp_bv v -> v
    | en, Exp_uop (opr, e) -> unopbv opr (evalexp en e)
    | en, Exp_bop (e1, opr, e2) -> binopbv (evalexp en e1) opr (evalexp en e2)
    | en, Exp_lop (e1, opr, e2) -> lopbv (evalexp en e1) opr (evalexp en e2)
    | en, Exp_cop (e, te, fs) ->
        (if equal_inta (fst (evalexp en e)) (Pos One) then evalexp en te
          else evalexp en fs)
    | en, Exp_rsn (e, n) -> bvrsn (evalexp en e) n
    | en, Exp_lsn (e, n) -> bvlsn (evalexp en e) n
    | en, Exp_bitslice (q, n2, n1) -> slicebv (getbvenv q en) n2 n1
    | en, Exp_bitsel (q, n) -> slicebv (getbvenv q en) n n
    | en, Exp_index (q, e) ->
        let index = nat (fst (evalexp en e)) in
        slicebv (getbvenv q en) index index;;

let rec toptocu
  en x1 = match en, x1 with
    en, Top_assign (d, el, e) ->
      (if null (senslexp e) && less_int d Zero_int
        then mkuevents en el (evalexp en e) else [])
    | uu, Top_in (v, va, vb) -> []
    | uu, Top_out (v, va, vb) -> []
    | uu, Top_io (v, va, vb) -> []
    | uu, Top_wire (v, va, vb) -> []
    | uu, Top_reg (v, va, vb) -> []
    | uu, Top_initial v -> []
    | uu, Top_always v -> [];;

let rec mkconfig
  tpl = (match tpl with [] -> initconfig
          | _ :: _ ->
            let en = fold (comp (fun a b -> a @ b) (updateenv [])) tpl [] in
            cfg_fute_update (fun _ -> toptofut Zero_nat tpl)
              (cfg_inacte_update
                (fun _ -> fold (comp (fun a b -> a @ b) (toptoinact en)) tpl [])
                (cfg_listne_update (fun _ -> toptole tpl)
                  (cfg_upde_update
                    (fun _ ->
                      fold (comp (fun a b -> a @ b) (toptocu en)) tpl [])
                    (cfg_actp_update (fun _ -> map toptoproc tpl)
                      (cfg_env_update (fun _ -> en) initconfig))))));;

let rec state p = let Prog_mod (_, a) = p in
                  mkconfig a;;

let rec cancel
  ev evl =
    (match evl with [] -> false
      | eva :: evla ->
        (match (ev, eva) with (Evt_upd (_, _), _) -> cancel ev evla
          | (Evt_updl (_, _), _) -> cancel ev evla
          | (Evt_inact _, _) -> cancel ev evla
          | (Evt_fut (_, Cpt_stm _), _) -> cancel ev evla
          | (Evt_fut (_, Cpt_alw (_, _)), _) -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [], _, _)), _) -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)), Evt_upd (_, _)) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)), Evt_updl (_, _)) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)), Evt_inact _) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_stm _))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_alw (_, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, [], _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name q1], _, _)),
              Evt_fut (_, Cpt_dca (_, [Exp_name q2], _, _)))
            -> (if equal_namea q1 q2 then true else cancel ev evla)
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, Exp_name _ :: _ :: _, _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, Exp_bv _ :: _, _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, Exp_uop (_, _) :: _, _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, Exp_bop (_, _, _) :: _, _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, Exp_lop (_, _, _) :: _, _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, Exp_cop (_, _, _) :: _, _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, Exp_rsn (_, _) :: _, _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, Exp_lsn (_, _) :: _, _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, Exp_bitslice (_, _, _) :: _, _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, Exp_bitsel (_, _) :: _, _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)),
              Evt_fut (_, Cpt_dca (_, Exp_index (_, _) :: _, _, _)))
            -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, [Exp_name _], _, _)), Evt_listn (_, _)) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, Exp_name _ :: _ :: _, _, _)), _) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, Exp_bv _ :: _, _, _)), _) -> cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, Exp_uop (_, _) :: _, _, _)), _) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, Exp_bop (_, _, _) :: _, _, _)), _) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, Exp_lop (_, _, _) :: _, _, _)), _) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, Exp_cop (_, _, _) :: _, _, _)), _) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, Exp_rsn (_, _) :: _, _, _)), _) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, Exp_lsn (_, _) :: _, _, _)), _) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, Exp_bitslice (_, _, _) :: _, _, _)), _) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, Exp_bitsel (_, _) :: _, _, _)), _) ->
            cancel ev evla
          | (Evt_fut (_, Cpt_dca (_, Exp_index (_, _) :: _, _, _)), _) ->
            cancel ev evla
          | (Evt_listn (_, _), _) -> cancel ev evla));;

let rec lenstm
  en x1 = match en, x1 with
    en, Stm_seq (k1, k2) ->
      plus_nat one_nat (plus_nat (lenstm en k1) (lenstm en k2))
    | en, Stm_cb (on, s) -> lenstm en s
    | en, Stm_ife (e, ts, fs) ->
        (if equal_inta (fst (evalexp en e)) (Pos One) then lenstm en ts
          else lenstm en fs)
    | en, Stm_while (e, s) ->
        (if equal_inta (fst (evalexp en e)) (Pos One) then lenstm en s
          else one_nat)
    | en, Stm_skip -> one_nat
    | en, Stm_finish -> one_nat
    | en, Stm_disab v -> one_nat
    | en, Stm_dba (v, va, vb) -> one_nat
    | en, Stm_tba (v, va, vb) -> one_nat
    | en, Stm_dnba (v, va, vb) -> one_nat
    | en, Stm_tnba (v, va, vb) -> one_nat
    | en, Stm_case (v, va, vb) -> one_nat
    | en, Stm_sensl (v, va) -> one_nat
    | en, Stm_delay (v, va) -> one_nat;;

let rec cfg_finish_update
  cfg_finisha
    (Configuration_ext
      (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
        cfg_listne, cfg_disabs, cfg_finish, more))
    = Configuration_ext
        (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
          cfg_listne, cfg_disabs, cfg_finisha cfg_finish, more);;

let rec cfg_disabs_update
  cfg_disabsa
    (Configuration_ext
      (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
        cfg_listne, cfg_disabs, cfg_finish, more))
    = Configuration_ext
        (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
          cfg_listne, cfg_disabsa cfg_disabs, cfg_finish, more);;

let rec cfg_listne
  (Configuration_ext
    (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
      cfg_listne, cfg_disabs, cfg_finish, more))
    = cfg_listne;;

let rec cfg_disabs
  (Configuration_ext
    (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
      cfg_listne, cfg_disabs, cfg_finish, more))
    = cfg_disabs;;

let rec sup_set _A
  x0 a = match x0, a with
    Coset xs, a -> Coset (filter (fun x -> not (member _A x a)) xs)
    | Set xs, a -> fold (insert _A) xs a;;

let rec cfg_nbaue_update
  cfg_nbauea
    (Configuration_ext
      (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
        cfg_listne, cfg_disabs, cfg_finish, more))
    = Configuration_ext
        (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte,
          cfg_nbauea cfg_nbaue, cfg_fute, cfg_listne, cfg_disabs, cfg_finish,
          more);;

let rec cfg_inacte
  (Configuration_ext
    (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
      cfg_listne, cfg_disabs, cfg_finish, more))
    = cfg_inacte;;

let rec cfg_nbaue
  (Configuration_ext
    (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
      cfg_listne, cfg_disabs, cfg_finish, more))
    = cfg_nbaue;;

let rec cfg_time
  (Configuration_ext
    (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
      cfg_listne, cfg_disabs, cfg_finish, more))
    = cfg_time;;

let rec cfg_fute
  (Configuration_ext
    (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
      cfg_listne, cfg_disabs, cfg_finish, more))
    = cfg_fute;;

let rec cfg_env
  (Configuration_ext
    (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
      cfg_listne, cfg_disabs, cfg_finish, more))
    = cfg_env;;

let rec sizeoflhs
  en x1 = match en, x1 with en, Exp_name q -> snd (getbvenv q en)
    | en, Exp_bitslice (q, n2, n1) -> plus_nat (minus_nat n2 n1) one_nat
    | en, Exp_bitsel (q, n) -> one_nat
    | en, Exp_index (q, e) -> one_nat
    | en, Exp_bv v -> Zero_nat
    | en, Exp_uop (v, va) -> Zero_nat
    | en, Exp_bop (v, va, vb) -> Zero_nat
    | en, Exp_lop (v, va, vb) -> Zero_nat
    | en, Exp_cop (v, va, vb) -> Zero_nat
    | en, Exp_rsn (v, va) -> Zero_nat
    | en, Exp_lsn (v, va) -> Zero_nat;;

let rec sizeofexp
  el en e =
    max ord_nat (fold (comp plus_nat (sizeoflhs en)) el Zero_nat)
      (snd (evalexp en e));;

let rec processnba
  s c = (match s with Stm_skip -> c | Stm_finish -> c | Stm_disab _ -> c
          | Stm_dba (_, _, _) -> c | Stm_tba (_, _, _) -> c
          | Stm_dnba (el, d, e) ->
            let bv = (fst (evalexp (cfg_env c) e), sizeofexp el (cfg_env c) e)
              in
            (if less_int d Zero_int
              then cfg_nbaue_update
                     (fun _ -> cfg_nbaue c @ mkuevents (cfg_env c) el bv) c
              else (if equal_inta d Zero_int
                     then cfg_inacte_update
                            (fun _ ->
                              cfg_inacte c @
                                [Evt_inact
                                   (Cpt_stm (Stm_dnba (el, Neg One, e)))])
                            c
                     else cfg_fute_update
                            (fun _ ->
                              addevent
                                (Evt_fut
                                  (plus_nat (nat d) (cfg_time c),
                                    Cpt_stm (Stm_dnba (el, Neg One, e))))
                                (cfg_fute c))
                            c))
          | Stm_tnba (el, sl, e) ->
            let sla =
              (if equal_list equal_sensit sl [Trg_star] then senslexp e else sl)
              in
            cfg_listne_update
              (fun _ ->
                cfg_listne c @
                  [Evt_listn (sla, Cpt_stm (Stm_dnba (el, Neg One, e)))])
              c
          | Stm_ife (_, _, _) -> c | Stm_while (_, _) -> c | Stm_cb (_, _) -> c
          | Stm_case (_, _, _) -> c | Stm_sensl (_, _) -> c
          | Stm_delay (_, _) -> c | Stm_seq (_, _) -> c);;

let rec cfg_actp
  (Configuration_ext
    (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
      cfg_listne, cfg_disabs, cfg_finish, more))
    = cfg_actp;;

let rec nameexp
  = function Exp_name q -> Some q
    | Exp_bitslice (q, n2, n1) -> Some q
    | Exp_bitsel (q, n) -> Some q
    | Exp_index (q, e) -> Some q
    | Exp_bv v -> None
    | Exp_uop (v, va) -> None
    | Exp_bop (v, va, vb) -> None
    | Exp_lop (v, va, vb) -> None
    | Exp_cop (v, va, vb) -> None
    | Exp_rsn (v, va) -> None
    | Exp_lsn (v, va) -> None;;

let rec remove _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: ys -> (if eq _A x y then ys else y :: remove _A x ys);;

let rec listminus _A
  la x1 = match la, x1 with la, [] -> la
    | la, y :: ys -> listminus _A (remove _A y la) ys;;

let rec letriger
  en q1 bvold bvnew trg =
    (match trg with Trg_star -> false
      | Trg_posed (Exp_name q2) ->
        less_int (fst (slicebv bvold Zero_nat Zero_nat))
          (fst (slicebv bvnew Zero_nat Zero_nat)) &&
          equal_namea q1 q2
      | Trg_posed (Exp_bv _) -> false | Trg_posed (Exp_uop (_, _)) -> false
      | Trg_posed (Exp_bop (_, _, _)) -> false
      | Trg_posed (Exp_lop (_, _, _)) -> false
      | Trg_posed (Exp_cop (_, _, _)) -> false
      | Trg_posed (Exp_rsn (_, _)) -> false
      | Trg_posed (Exp_lsn (_, _)) -> false
      | Trg_posed (Exp_bitslice (_, _, _)) -> false
      | Trg_posed (Exp_bitsel (q2, n)) ->
        less_int (fst (slicebv bvold n n)) (fst (slicebv bvnew n n)) &&
          equal_namea q1 q2
      | Trg_posed (Exp_index (q2, e)) ->
        let n = nat (fst (evalexp en e)) in
        less_int (fst (slicebv bvold n n)) (fst (slicebv bvnew n n)) &&
          equal_namea q1 q2
      | Trg_neged (Exp_name q2) ->
        less_int (fst (slicebv bvnew Zero_nat Zero_nat))
          (fst (slicebv bvold Zero_nat Zero_nat)) &&
          equal_namea q1 q2
      | Trg_neged (Exp_bv _) -> false | Trg_neged (Exp_uop (_, _)) -> false
      | Trg_neged (Exp_bop (_, _, _)) -> false
      | Trg_neged (Exp_lop (_, _, _)) -> false
      | Trg_neged (Exp_cop (_, _, _)) -> false
      | Trg_neged (Exp_rsn (_, _)) -> false
      | Trg_neged (Exp_lsn (_, _)) -> false
      | Trg_neged (Exp_bitslice (_, _, _)) -> false
      | Trg_neged (Exp_bitsel (q2, n)) ->
        less_int (fst (slicebv bvnew n n)) (fst (slicebv bvold n n)) &&
          equal_namea q1 q2
      | Trg_neged (Exp_index (q2, e)) ->
        let n = nat (fst (evalexp en e)) in
        less_int (fst (slicebv bvnew n n)) (fst (slicebv bvold n n)) &&
          equal_namea q1 q2
      | Trg_exp a ->
        (match a with Exp_name aa -> equal_namea q1 aa | Exp_bv _ -> false
          | Exp_uop (_, _) -> false | Exp_bop (_, _, _) -> false
          | Exp_lop (_, _, _) -> false | Exp_cop (_, _, _) -> false
          | Exp_rsn (_, _) -> false | Exp_lsn (_, _) -> false
          | Exp_bitslice (q2, n2, n1) ->
            not (equal_inta (fst (slicebv bvold n2 n1))
                  (fst (slicebv bvnew n2 n1))) &&
              equal_namea q1 q2
          | Exp_bitsel (q2, n) ->
            not (equal_inta (fst (slicebv bvold n n))
                  (fst (slicebv bvnew n n))) &&
              equal_namea q1 q2
          | Exp_index (q2, e) ->
            let n = nat (fst (evalexp en e)) in
            not (equal_inta (fst (slicebv bvold n n))
                  (fst (slicebv bvnew n n))) &&
              equal_namea q1 q2));;

let rec isletrgd
  en q bvold bvnew ev =
    (match ev with Evt_upd (_, _) -> false | Evt_updl (_, _) -> false
      | Evt_inact _ -> false | Evt_fut (_, _) -> false
      | Evt_listn (trgs, _) ->
        not (null (filter (letriger en q bvold bvnew) trgs)));;

let rec trglevents
  en q bvo bvn le =
    (match le with [] -> []
      | ev :: evl ->
        (if isletrgd en q bvo bvn ev then ev :: trglevents en q bvo bvn evl
          else trglevents en q bvo bvn evl));;

let rec letoprocbv
  en ev =
    (match ev with Evt_upd (_, _) -> Cpt_stm Stm_skip
      | Evt_updl (_, _) -> Cpt_stm Stm_skip | Evt_inact _ -> Cpt_stm Stm_skip
      | Evt_fut (_, _) -> Cpt_stm Stm_skip
      | Evt_listn (sl, Cpt_stm statement) -> Cpt_alw (sl, Cpt_stm statement)
      | Evt_listn (sl, Cpt_alw (lista, process)) ->
        Cpt_alw (sl, Cpt_alw (lista, process))
      | Evt_listn (_, Cpt_dca (d, el, e, _)) ->
        Cpt_dca (d, el, e, Exp_bv (evalexp en e)));;

let rec updateconfig
  q bvo bvn c =
    let (en, le) = (cfg_env c, cfg_listne c) in
    let tle = trglevents en q bvo bvn le in
    let ntle = listminus equal_event le tle in
    cfg_listne_update (fun _ -> ntle)
      (cfg_actp_update (fun _ -> cfg_actp c @ map (letoprocbv en) tle) c);;

let rec addbinding
  x0 b = match x0, b with [], b -> [b]
    | p :: pl, b ->
        (if equal_namea (fst p) (fst b) then b :: pl
          else p :: addbinding pl b);;

let rec updatevar
  en e bv =
    (match e
      with Exp_name q ->
        addbinding en
          (q, slicebv bv (minus_nat (snd (getbvenv q en)) one_nat) Zero_nat)
      | Exp_bv _ -> en | Exp_uop (_, _) -> en | Exp_bop (_, _, _) -> en
      | Exp_lop (_, _, _) -> en | Exp_cop (_, _, _) -> en | Exp_rsn (_, _) -> en
      | Exp_lsn (_, _) -> en
      | Exp_bitslice (q, n2, n1) ->
        addbinding en (q, slicebva (getbvenv q en) bv n2 n1)
      | Exp_bitsel (q, n) -> addbinding en (q, slicebva (getbvenv q en) bv n n)
      | Exp_index (q, ea) ->
        addbinding en
          (q, slicebva (getbvenv q en) bv (nat (fst (evalexp en ea)))
                (nat (fst (evalexp en ea)))));;

let rec processue
  c evl =
    (match evl with [] -> c
      | Evt_upd (e, bvn) :: evla ->
        (match nameexp e with None -> c
          | Some q ->
            let bvo = getbvenv q (cfg_env c) in
            (if not (equal_proda equal_int equal_nat bvo bvn)
              then let ca =
                     cfg_env_update (fun _ -> updatevar (cfg_env c) e bvn) c in
                   let cb = updateconfig q bvo bvn ca in
                   processue cb evla
              else c))
      | Evt_updl (_, _) :: _ -> c | Evt_inact _ :: _ -> c
      | Evt_fut (_, _) :: _ -> c | Evt_listn (_, _) :: _ -> c);;

let rec processba
  c s = (match s with Stm_skip -> c | Stm_finish -> c | Stm_disab _ -> c
          | Stm_dba (el, d, e) ->
            let bv = (fst (evalexp (cfg_env c) e), sizeofexp el (cfg_env c) e)
              in
            (if less_int d Zero_int
              then processue c (mkuevents (cfg_env c) el bv)
              else (if equal_inta d Zero_int
                     then cfg_inacte_update
                            (fun _ ->
                              cfg_inacte c @
                                [Evt_inact
                                   (Cpt_stm (Stm_dba (el, Neg One, e)))])
                            c
                     else cfg_fute_update
                            (fun _ ->
                              addevent
                                (Evt_fut
                                  (plus_nat (nat d) (cfg_time c),
                                    Cpt_stm (Stm_dba (el, Neg One, e))))
                                (cfg_fute c))
                            c))
          | Stm_tba (el, sl, e) ->
            let _ =
              (if equal_list equal_sensit sl [Trg_star] then senslexp e else sl)
              in
            cfg_listne_update
              (fun _ ->
                cfg_listne c @
                  [Evt_listn (sl, Cpt_stm (Stm_dba (el, Neg One, e)))])
              c
          | Stm_dnba (_, _, _) -> c | Stm_tnba (_, _, _) -> c
          | Stm_ife (_, _, _) -> c | Stm_while (_, _) -> c | Stm_cb (_, _) -> c
          | Stm_case (_, _, _) -> c | Stm_sensl (_, _) -> c
          | Stm_delay (_, _) -> c | Stm_seq (Stm_skip, _) -> c
          | Stm_seq (Stm_finish, _) -> c | Stm_seq (Stm_disab _, _) -> c
          | Stm_seq (Stm_dba (el, d, e), k) ->
            let bv = (fst (evalexp (cfg_env c) e), sizeofexp el (cfg_env c) e)
              in
            let ca = processue c (mkuevents (cfg_env c) el bv) in
            (if less_int d Zero_int
              then cfg_actp_update (fun _ -> cfg_actp ca @ [Cpt_stm k]) ca
              else (if equal_inta d Zero_int
                     then cfg_inacte_update
                            (fun _ ->
                              cfg_inacte c @
                                [Evt_inact
                                   (Cpt_stm
                                     (Stm_seq (Stm_dba (el, Neg One, e), k)))])
                            c
                     else cfg_fute_update
                            (fun _ ->
                              addevent
                                (Evt_fut
                                  (plus_nat (nat d) (cfg_time c),
                                    Cpt_stm
                                      (Stm_seq (Stm_dba (el, Neg One, e), k))))
                                (cfg_fute c))
                            c))
          | Stm_seq (Stm_tba (el, sl, e), k) ->
            let _ =
              (if equal_list equal_sensit sl [Trg_star] then senslexp e else sl)
              in
            cfg_listne_update
              (fun _ ->
                cfg_listne c @
                  [Evt_listn
                     (sl, Cpt_stm (Stm_seq (Stm_dba (el, Neg One, e), k)))])
              c
          | Stm_seq (Stm_dnba (_, _, _), _) -> c
          | Stm_seq (Stm_tnba (_, _, _), _) -> c
          | Stm_seq (Stm_ife (_, _, _), _) -> c
          | Stm_seq (Stm_while (_, _), _) -> c | Stm_seq (Stm_cb (_, _), _) -> c
          | Stm_seq (Stm_case (_, _, _), _) -> c
          | Stm_seq (Stm_sensl (_, _), _) -> c
          | Stm_seq (Stm_delay (_, _), _) -> c
          | Stm_seq (Stm_seq (_, _), _) -> c);;

let rec execstm
  x0 c = match x0, c with Stm_finish, c -> cfg_finish_update (fun _ -> true) c
    | Stm_disab q, c ->
        cfg_disabs_update
          (fun _ ->
            sup_set equal_name (cfg_disabs c) (insert equal_name q bot_set))
          c
    | Stm_seq (Stm_dba (el, d, e), k), c ->
        processba c (Stm_seq (Stm_dba (el, d, e), k))
    | Stm_seq (Stm_tba (el, sl, e), k), c ->
        processba c (Stm_seq (Stm_tba (el, sl, e), k))
    | Stm_dba (el, d, e), c -> processba c (Stm_dba (el, d, e))
    | Stm_tba (el, sl, e), c -> processba c (Stm_tba (el, sl, e))
    | Stm_seq (Stm_dnba (el, d, e), k), c ->
        processnba (Stm_dnba (el, d, e)) (execstm k c)
    | Stm_seq (Stm_tnba (el, sl, e), k), c ->
        processnba (Stm_tnba (el, sl, e)) (execstm k c)
    | Stm_dnba (el, d, e), c -> processnba (Stm_dnba (el, d, e)) c
    | Stm_tnba (el, sl, e), c -> processnba (Stm_tnba (el, sl, e)) c
    | Stm_sensl (sl, s), c ->
        let _ =
          (if equal_list equal_sensit sl [Trg_star] then senslstm s else sl) in
        cfg_listne_update (fun _ -> Evt_listn (sl, Cpt_stm s) :: cfg_listne c) c
    | Stm_seq (Stm_skip, s2), c -> execstm s2 (execstm Stm_skip c)
    | Stm_seq (Stm_finish, s2), c -> execstm s2 (execstm Stm_finish c)
    | Stm_seq (Stm_disab v, s2), c -> execstm s2 (execstm (Stm_disab v) c)
    | Stm_seq (Stm_ife (v, va, vb), s2), c ->
        execstm s2 (execstm (Stm_ife (v, va, vb)) c)
    | Stm_seq (Stm_while (v, va), s2), c ->
        execstm s2 (execstm (Stm_while (v, va)) c)
    | Stm_seq (Stm_cb (v, va), s2), c -> execstm s2 (execstm (Stm_cb (v, va)) c)
    | Stm_seq (Stm_case (v, va, vb), s2), c ->
        execstm s2 (execstm (Stm_case (v, va, vb)) c)
    | Stm_seq (Stm_sensl (v, va), s2), c ->
        execstm s2 (execstm (Stm_sensl (v, va)) c)
    | Stm_seq (Stm_delay (v, va), s2), c ->
        execstm s2 (execstm (Stm_delay (v, va)) c)
    | Stm_seq (Stm_seq (v, va), s2), c ->
        execstm s2 (execstm (Stm_seq (v, va)) c)
    | Stm_skip, c -> c
    | Stm_ife (v, va, vb), c -> c
    | Stm_while (v, va), c -> c
    | Stm_cb (v, va), c -> c
    | Stm_case (v, va, vb), c -> c
    | Stm_delay (v, va), c -> c;;

let rec cfg_upde
  (Configuration_ext
    (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
      cfg_listne, cfg_disabs, cfg_finish, more))
    = cfg_upde;;

let rec processevent
  x0 c = match x0, c with
    Evt_updl (evl, k), c ->
      let ca = processue c evl in
      cfg_actp_update (fun _ -> [k] @ cfg_actp ca) ca
    | Evt_upd (e, bv), c -> processue c [Evt_upd (e, bv)]
    | Evt_inact v, c -> c
    | Evt_fut (v, va), c -> c
    | Evt_listn (v, va), c -> c;;

let rec processevents
  evl c = fold processevent evl (cfg_upde_update (fun _ -> []) c);;

let rec letoproc
  ev = (match ev with Evt_upd (_, _) -> Cpt_stm Stm_skip
         | Evt_updl (_, _) -> Cpt_stm Stm_skip | Evt_inact _ -> Cpt_stm Stm_skip
         | Evt_fut (_, _) -> Cpt_stm Stm_skip
         | Evt_listn (sl, a) ->
           (match a with Cpt_stm statement -> Cpt_alw (sl, Cpt_stm statement)
             | Cpt_alw (lista, process) ->
               Cpt_alw (sl, Cpt_alw (lista, process))
             | Cpt_dca (aa, b, c, d) -> Cpt_dca (aa, b, c, d)));;

let rec countcpt
  en x1 = match en, x1 with en, Cpt_stm s -> lenstm en s
    | en, Cpt_alw (sl, k) -> countcpt en k
    | en, Cpt_dca (uu, uv, uw, ux) -> one_nat;;

let rec countcptel
  en el =
    (match el with [] -> Zero_nat
      | e :: ela -> plus_nat (countcpt en (letoproc e)) (countcptel en ela));;

let rec countcptpl
  en pl =
    (match pl with [] -> Zero_nat
      | p :: pla -> plus_nat (countcpt en p) (countcptpl en pla));;

let rec evalcase
  en s =
    (match s with Stm_skip -> s | Stm_finish -> s | Stm_disab _ -> s
      | Stm_dba (_, _, _) -> s | Stm_tba (_, _, _) -> s
      | Stm_dnba (_, _, _) -> s | Stm_tnba (_, _, _) -> s
      | Stm_ife (_, _, _) -> s | Stm_while (_, _) -> s | Stm_cb (_, _) -> s
      | Stm_case (e, cl, ds) ->
        (match cl with [] -> evalcase en ds
          | c :: cla ->
            (if equal_inta (fst (evalexp en e)) (fst (evalexp en (fst c)))
              then evalcase en (snd c)
              else evalcase en (Stm_case (e, cla, ds))))
      | Stm_sensl (_, _) -> s | Stm_delay (_, _) -> s | Stm_seq (_, _) -> s);;

let rec stepstm
  c s = (match s with Stm_skip -> s | Stm_finish -> s | Stm_disab _ -> s
          | Stm_dba (_, _, _) -> s | Stm_tba (_, _, _) -> s
          | Stm_dnba (_, _, _) -> s | Stm_tnba (_, _, _) -> s
          | Stm_ife (e, ts, fs) ->
            (if equal_inta (fst (evalexp (cfg_env c) e)) (Pos One)
              then stepstm c ts else stepstm c fs)
          | Stm_while (e, sa) ->
            (if equal_inta (fst (evalexp (cfg_env c) e)) (Pos One)
              then stepstm c sa else Stm_skip)
          | Stm_cb (None, sa) -> stepstm c sa
          | Stm_cb (Some q, sa) ->
            (if member equal_name q (cfg_disabs c) then Stm_skip
              else stepstm c sa)
          | Stm_case (_, _, _) -> evalcase (cfg_env c) s | Stm_sensl (_, _) -> s
          | Stm_delay (_, _) -> s
          | Stm_seq (s1, a) -> Stm_seq (stepstm c s1, a));;

let rec execproc
  t x1 c = match t, x1, c with
    t, Cpt_stm s, c ->
      let ca = execstm (stepstm c s) c in
      let ta =
        plus_nat (countcptpl (cfg_env ca) (cfg_actp ca))
          (countcptel (cfg_env ca) (cfg_listne ca))
        in
      (match (cfg_actp ca, less_nat ta t) with ([], _) -> ca
        | (p :: pl, true) ->
          fold (execproc ta) (p :: pl) (cfg_actp_update (fun _ -> []) ca)
        | (_ :: _, false) -> ca)
    | t, Cpt_alw (sl, k), c ->
        let ca = execproc t k c in
        cfg_listne_update (fun _ -> cfg_listne ca @ [Evt_listn (sl, k)]) ca
    | t, Cpt_dca (d, el, ea, e), c ->
        let ca =
          (if less_int d Zero_int then execstm (Stm_dba (el, Neg One, e)) c
            else execstm (Stm_delay (nat d, Stm_dba (el, Neg One, e))) c)
          in
        let ta =
          plus_nat (countcptpl (cfg_env ca) (cfg_actp ca))
            (countcptel (cfg_env ca) (cfg_listne ca))
          in
        (match (cfg_actp ca, less_nat ta t)
          with ([], _) ->
            cfg_listne_update
              (fun _ ->
                cfg_listne ca @
                  [Evt_listn (senslexp ea, Cpt_dca (d, el, ea, ea))])
              ca
          | (p :: pl, true) ->
            let cb =
              fold (execproc ta) (p :: pl) (cfg_actp_update (fun _ -> []) ca) in
            cfg_listne_update
              (fun _ ->
                cfg_listne cb @
                  [Evt_listn (senslexp ea, Cpt_dca (d, el, ea, ea))])
              (cfg_actp_update (fun _ -> []) cb)
          | (_ :: _, false) -> ca);;

let rec execprocs
  x0 c = match x0, c with [], c -> c
    | p :: xs, c ->
        let t =
          plus_nat (countcpt (cfg_env c) p)
            (countcptel (cfg_env c) (cfg_listne c))
          in
        execprocs xs (execproc t p c);;

let rec activate
  e = (match e with Evt_upd (_, _) -> Cpt_stm Stm_skip
        | Evt_updl (_, _) -> Cpt_stm Stm_skip | Evt_inact k -> k
        | Evt_fut (_, _) -> Cpt_stm Stm_skip
        | Evt_listn (_, _) -> Cpt_stm Stm_skip);;

let rec stepsim
  c = let cap = processevents (cfg_upde c) (cfg_upde_update (fun _ -> []) c) in
      let cie = execprocs (cfg_actp cap) (cfg_actp_update (fun _ -> []) cap) in
      let pl = map activate (cfg_inacte cie) in
      let cnba =
        execprocs pl
          (cfg_inacte_update (fun _ -> []) (cfg_actp_update (fun _ -> []) cie))
        in
      let cfinal =
        processevents [Evt_updl (cfg_nbaue cnba, Cpt_stm Stm_skip)]
          (cfg_nbaue_update (fun _ -> []) (cfg_upde_update (fun _ -> []) cnba))
        in
      execprocs (cfg_actp cfinal) (cfg_actp_update (fun _ -> []) cfinal);;

let rec initargs
  en x1 = match en, x1 with en, [] -> []
    | en, a :: argl ->
        let s = snd (getbvenv (fst a) en) in
        [Cpt_stm (Stm_dba ([Exp_name (fst a)], Neg One, Exp_bv (snd a, s)))] @
          initargs en argl;;

let rec fedinput
  argl c = cfg_actp_update (fun _ -> initargs (cfg_env c) argl @ cfg_actp c) c;;

let addintalw : program
  = Prog_mod
      ([Xi; Yi],
        [Top_in (nat_of_num (Bit1 (Bit1 One)), Zero_nat, [Xi; Yi]);
          Top_wire (nat_of_num (Bit1 (Bit1 One)), Zero_nat, [X; Y]);
          Top_reg (nat_of_num (Bit1 (Bit1 One)), Zero_nat, [Z]);
          Top_assign (Zero_int, [Exp_name X], Exp_name Xi);
          Top_assign (Zero_int, [Exp_name Y], Exp_name Yi);
          Top_always
            (Stm_delay
              (nat_of_num (Bit0 One),
                Stm_cb
                  (None,
                    Stm_seq
                      (Stm_dba
                         ([Exp_name Z], Neg One,
                           Exp_bop (Exp_name X, BvsPLUS, Exp_name Y)),
                        Stm_finish))))]);;

let rec cfg_finish
  (Configuration_ext
    (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
      cfg_listne, cfg_disabs, cfg_finish, more))
    = cfg_finish;;

let rec nextcycleb
  c = null (cfg_upde c) &&
        (null (cfg_actp c) &&
          (null (cfg_inacte c) &&
            (null (cfg_nbaue c) &&
              (not (null (cfg_fute c)) && not (cfg_finish c)))));;

let rec nextpassb
  c = (not (null (cfg_upde c)) ||
        (not (null (cfg_actp c)) ||
          (not (null (cfg_inacte c)) || not (null (cfg_nbaue c))))) &&
        not (cfg_finish c);;

let rec cfg_time_update
  cfg_timea
    (Configuration_ext
      (cfg_env, cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue, cfg_fute,
        cfg_listne, cfg_disabs, cfg_finish, more))
    = Configuration_ext
        (cfg_env, cfg_timea cfg_time, cfg_actp, cfg_upde, cfg_inacte, cfg_nbaue,
          cfg_fute, cfg_listne, cfg_disabs, cfg_finish, more);;

let rec timeofhd evl = (match evl with [] -> Zero_nat | ev :: _ -> timeof ev);;

let rec cancelling
  evl = (match evl with [] -> []
          | e :: evla ->
            (if cancel e evla then cancelling evla else e :: cancelling evla));;

let rec futtoproc
  e = (match e with Evt_upd (_, _) -> Cpt_stm Stm_skip
        | Evt_updl (_, _) -> Cpt_stm Stm_skip | Evt_inact _ -> Cpt_stm Stm_skip
        | Evt_fut (_, k) -> k | Evt_listn (_, _) -> Cpt_stm Stm_skip);;

let rec newcycle
  c = let fe = cancelling (cfg_fute c) in
      let nt = timeofhd fe in
      let fea = filter (awake nt) fe in
      cfg_time_update (fun _ -> nt)
        (cfg_fute_update (fun _ -> listminus equal_event fe fea)
          (cfg_actp_update (fun _ -> map futtoproc fea) c));;

let rec simulate
  m c = (match (less_nat Zero_nat m, (nextcycleb c, nextpassb c))
          with (true, (true, _)) ->
            simulate (minus_nat m one_nat) (stepsim (newcycle c))
          | (true, (false, true)) -> simulate (minus_nat m one_nat) (stepsim c)
          | (true, (false, false)) -> c | (false, (_, true)) -> stepsim c
          | (false, (_, false)) -> c);;

let evaluate : int
  = let c =
      simulate (nat_of_num (Bit0 One))
        (fedinput [(Xi, Pos (Bit0 One)); (Yi, Pos (Bit1 (Bit0 One)))]
          (state addintalw))
      in
    fst (getbvenv Z (cfg_env c));;

end;; (*struct Evaluate*)
