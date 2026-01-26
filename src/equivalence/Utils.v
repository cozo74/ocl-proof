From Stdlib Require Import Ascii Arith String ZArith Reals.
From Stdlib Require Import Logic.FunctionalExtensionality.


(* Total maps *)

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).


Definition t_update {A : Type} (m : total_map A)
  (x : string) (v : A) :=
fun x' => if String.eqb x x' then v else m x'.


Lemma t_update_eq : forall A (m : total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros. unfold t_update. rewrite String.eqb_refl. reflexivity.
Qed.


Lemma t_update_neq : forall A (m : total_map A) x y v,
  x <> y ->
  (t_update m x v) y = m y.
Proof.
  intros. unfold t_update.
  destruct (String.eqb y x) eqn:Heq.
  - apply String.eqb_eq in Heq. subst. contradiction.
  - apply String.eqb_neq in H. rewrite H. reflexivity.
Qed.


Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (t_empty v) x = v.
Proof.
  intros. unfold t_empty. reflexivity.
Qed.


Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  t_update (t_update m x v1) x v2 = t_update m x v2.
Proof.
  intros A m x v1 v2.
  apply functional_extensionality; intro y.
  unfold t_update.
  destruct (String.eqb x y) eqn:Heq; reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  t_update m x (m x) = m.
Proof.
  intros A m x.
  apply functional_extensionality; intro y.
  destruct (String.eqb x y) eqn:Heq.
  - (* y = x *)
    apply String.eqb_eq in Heq. subst.
    rewrite t_update_eq.
    reflexivity.
  - (* y <> x *)
    apply String.eqb_neq in Heq.
    rewrite t_update_neq by assumption.
    reflexivity.
Qed.


Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (t_update (t_update m x2 v2) x1 v1) = (t_update (t_update m x1 v1) x2 v2).

Proof.
  intros A m v1 v2 x1 x2 Hneq.
  apply functional_extensionality; intro y.

  destruct (String.eqb x1 y) eqn:Hx1y.
  - (* y = x1 *)
    apply String.eqb_eq in Hx1y; subst y.
    rewrite t_update_eq.                     (* LHS -> v1 *)
    rewrite t_update_neq by assumption.      (* RHS: inner update at x2 doesn't affect x1 *)
    rewrite t_update_eq.                     (* RHS -> v1 *)
    reflexivity.

  - (* y <> x1 *)
    apply String.eqb_neq in Hx1y.
    rewrite t_update_neq by assumption.      (* LHS: outer update at x1 doesn't affect y *)

    destruct (String.eqb x2 y) eqn:Hx2y.
    + (* y = x2 *)
      apply String.eqb_eq in Hx2y; subst y.
      rewrite t_update_eq.                   (* LHS -> v2 *)
      rewrite t_update_eq.                   (* RHS outer update at x2 -> v2 *)
      reflexivity.

    + (* y <> x2 *)
      apply String.eqb_neq in Hx2y.
      rewrite t_update_neq by assumption.    (* LHS inner update at x2 doesn't affect y *)
      rewrite t_update_neq by assumption.    (* RHS outer update at x2 doesn't affect y *)
      rewrite t_update_neq by assumption.    (* RHS inner update at x1 doesn't affect y *)
      reflexivity.
Qed.



(* Partial maps *)


Definition partial_map (A : Type) := total_map (option A).


Definition empty {A : Type} : partial_map A :=
  t_empty None.


Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (t_update m x (Some v)).

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.


Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.



Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq.
  - reflexivity.
  - apply H.
Qed.


Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.


Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  update m x v = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  update (update m x2 v2) x1 v1 = update (update m x1 v1) x2 v2.
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.



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

