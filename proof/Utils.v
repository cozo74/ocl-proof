From Stdlib Require Import Ascii Arith String ZArith Reals.



Definition total_map (A : Type) := string -> A.
Definition empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition update {A : Type} (m : total_map A)
  (x : string) (v : A) :=
fun x' => if String.eqb x x' then v else m x'.




Definition Rfloor_real (r : R) (z : Z) : Prop :=
  (IZR z <= r < IZR (z + 1))%R.



Definition Rround_real (r : R) (z : Z) : Prop :=
Rfloor_real (r + /2) z.



Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (f c) (map_string f rest)
  end.



(* 单字符转大写 *)
Definition toUpper_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if andb (65 <=? n) (n <=? 90) then
      ascii_of_nat n
  else if andb (97 <=? n) (n <=? 122) then
      ascii_of_nat (n - 32)
  else c.

(* 单字符转小写 *)
Definition toLower_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if andb (97 <=? n) (n <=? 122) then
      ascii_of_nat n
  else if andb (65 <=? n) (n <=? 90) then
      ascii_of_nat (n + 32)
  else c.

Definition toUpper (s : string) : string :=
  map_string toUpper_char s.

Definition toLower (s : string) : string :=
  map_string toLower_char s.




Definition Rleb (x y : R) : bool :=
if Rle_dec x y then true else false.

Definition Rltb (x y : R) : bool :=
if Rlt_dec x y then true else false.


Definition Rge_dec (x y : R) := Rle_dec y x.
Definition Rgt_dec (x y : R) := Rlt_dec y x.

Definition Rgeb (x y : R) : bool :=
  if Rge_dec x y then true else false.

Definition Rgtb (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition Reqb (x y : R) : bool :=
  if Req_EM_T x y then true else false.

Definition Rneqb (x y : R) : bool :=
  if Req_EM_T x y then false else true.

