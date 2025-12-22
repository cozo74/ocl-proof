From Stdlib Require Import Ascii Arith String ZArith Reals.



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