
From Stdlib Require Import String ZArith Reals List.
Import ListNotations.

From OCL.equivalence Require Import OCLSyntax Utils Models.
Open Scope string_scope.

(* ================================= Operational Semantics ======================================= *)







Definition bool_unop_sem (op : bool_unop) (v : I_e) : option I_e :=
  match op, v with
  | UNot, Ie_Single (Ih_Basic (Ib_Bool b)) => Some (Ie_Single (Ih_Basic (Ib_Bool (negb b))))
  | _, _ => None
  end.

Definition half : R := (1 / 2).

Definition round_Z (r : R) : Z :=
  if Rlt_dec r 0
  then Z.opp (Int_part ((- r) + half))
  else Int_part (r + half).


Definition arith_unop_sem (op : arith_unop) (v : I_e) : option I_e :=
  match op, v with
  | UNeg,   Ie_Single (Ih_Basic (Ib_Int n))  => Some (Ie_Single (Ih_Basic (Ib_Int (-n))))
  | UAbs,   Ie_Single (Ih_Basic (Ib_Int n))  => Some (Ie_Single (Ih_Basic (Ib_Int (Z.abs n))))

  | UNeg,   Ie_Single (Ih_Basic (Ib_Real r)) => Some (Ie_Single (Ih_Basic (Ib_Real (-r))))
  | UAbs,   Ie_Single (Ih_Basic (Ib_Real r)) => Some (Ie_Single (Ih_Basic (Ib_Real (Rabs r))))

  | UFloor, Ie_Single (Ih_Basic (Ib_Real r)) => Some (Ie_Single (Ih_Basic (Ib_Int (Int_part r))))
  | URound, Ie_Single (Ih_Basic (Ib_Real r)) => Some (Ie_Single (Ih_Basic (Ib_Int (round_Z r))))

  | _, _ => None
  end.


Definition str_unop_sem (op : str_unop) (v : I_e) : option I_e :=
  match op, v with
  | UToUpper, Ie_Single (Ih_Basic (Ib_String s)) => Some (Ie_Single (Ih_Basic (Ib_String (toUpper s))))
  | UToLower, Ie_Single (Ih_Basic (Ib_String s)) => Some (Ie_Single (Ih_Basic (Ib_String (toLower s))))
  | USize,    Ie_Single (Ih_Basic (Ib_String s)) => Some (Ie_Single (Ih_Basic (Ib_Int (Z.of_nat (String.length s)))))
  
  | _, _ => None
  end.




Definition unop_sem (op : unop) (v1 : I_e) : option I_e :=
  match op with
  | U_Bool  o => bool_unop_sem  o v1
  | U_Arith o => arith_unop_sem o v1
  | U_Str   o => str_unop_sem   o v1
  end.









Definition bool_binop_sem (op : bool_binop) (b1 b2 : I_e) : option I_e :=
  match op, b1, b2 with
  | BAnd,     
    Ie_Single (Ih_Basic (Ib_Bool b1)),
    Ie_Single (Ih_Basic (Ib_Bool b2)) => Some (Ie_Single (Ih_Basic (Ib_Bool (andb b1 b2))))

  | BOr,      
    Ie_Single (Ih_Basic (Ib_Bool b1)), 
    Ie_Single (Ih_Basic (Ib_Bool b2)) => Some (Ie_Single (Ih_Basic (Ib_Bool (orb b1 b2))))

  | BXor,     
    Ie_Single (Ih_Basic (Ib_Bool b1)), 
    Ie_Single (Ih_Basic (Ib_Bool b2)) => Some (Ie_Single (Ih_Basic (Ib_Bool (xorb b1 b2))))

  | BImplies, 
    Ie_Single (Ih_Basic (Ib_Bool b1)), 
    Ie_Single (Ih_Basic (Ib_Bool b2)) => Some (Ie_Single (Ih_Basic (Ib_Bool (orb (negb b1) b2))))

  | _, _, _ => None
  end.







Definition comp_eq_sem (v1 v2 : I_e) : option bool :=
  match v1, v2 with
  | Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Int b))        => Some (a =? b)%Z
  | Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Real b))      => Some (Reqb (IZR a) b)
  | Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Int b))      => Some (Reqb a (IZR b))
  | Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Real b))     => Some (Reqb a b)
  | Ie_Single (Ih_Basic (Ib_String a)), Ie_Single (Ih_Basic (Ib_String b)) => Some (String.eqb a b)
  | Ie_Single (Ih_Object  c1 a), Ie_Single (Ih_Object  c2 b) => Some (andb (String.eqb c1 c2) (String.eqb a b))
  | _, _ => None
  end.





Definition comp_lt_sem (v1 v2 : I_e) : option bool :=
  match v1, v2 with
  | Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Int b))    => Some (a <? b)%Z
  | Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Real b))  => Some (Rltb (IZR a) b)
  | Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Int b))  => Some (Rltb a (IZR b))
  | Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Real b)) => Some (Rltb a b)
  | _, _ => None
  end.



Definition comp_le_sem (v1 v2 : I_e) : option bool :=
  match v1, v2 with
  | Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Int b))    => Some (a <=? b)%Z
  | Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Real b))  => Some (Rleb (IZR a) b)
  | Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Int b))  => Some (Rleb a (IZR b))
  | Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Real b)) => Some (Rleb a b)
  | _, _ => None
  end.

Definition lift_bool_Ie (ob : option bool) : option I_e :=
  option_map (fun b => Ie_Single (Ih_Basic (Ib_Bool b))) ob.
  
Definition comp_binop_sem
  (op : comp_binop) (v1 v2 : I_e) : option I_e :=
  lift_bool_Ie (
  match op with
  | BEq => comp_eq_sem v1 v2
  | BNe => option_map negb (comp_eq_sem v1 v2)
  | BLt => comp_lt_sem v1 v2
  | BLe => comp_le_sem v1 v2
  | BGt => comp_lt_sem v2 v1
  | BGe => comp_le_sem v2 v1
  end
  ).


Definition arith_binop_sem
  (op : arith_binop) (v1 v2 : I_e) : option I_e :=
  match op, v1, v2 with
  | BAdd, Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Int b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Int (a + b)%Z)))

  | BAdd, Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Real b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Real (IZR a + b))))

  | BAdd, Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Int b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Real (a + IZR b))))

  | BAdd, Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Real b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Real (a + b))))

  | BSub,Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Int b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Int (a - b)%Z)))

  | BSub, Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Real b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Real (IZR a - b))))

  | BSub, Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Int b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Real (a - IZR b))))

  | BSub, Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Real b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Real (a - b))))

  | BMul, Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Int b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Int (a * b)%Z)))

  | BMul, Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Real b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Real ((IZR a) * b))))

  | BMul, Ie_Single(Ih_Basic(Ib_Real a)), Ie_Single(Ih_Basic(Ib_Int b)) =>
      Some(Ie_Single(Ih_Basic(Ib_Real(a * IZR b))))

  | BMul, Ie_Single(Ih_Basic(Ib_Real a)), Ie_Single(Ih_Basic(Ib_Real b)) =>
      Some(Ie_Single(Ih_Basic(Ib_Real(a * b))))

  | BDiv, Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Int b)) =>
      if Z.eqb b 0 then None
      else Some (Ie_Single (Ih_Basic (Ib_Real (IZR a / IZR b))))

  | BDiv, Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Real b)) =>
      if Reqb b 0 then None
      else Some (Ie_Single (Ih_Basic (Ib_Real (IZR a / b))))

  | BDiv, Ie_Single(Ih_Basic(Ib_Real a)), Ie_Single(Ih_Basic(Ib_Int b)) =>
      if Z.eqb b 0 then None
      else Some (Ie_Single (Ih_Basic (Ib_Real (a / IZR b))))

  | BDiv, Ie_Single(Ih_Basic(Ib_Real a)), Ie_Single(Ih_Basic(Ib_Real b)) =>
      if Reqb b 0 then None
      else Some (Ie_Single (Ih_Basic (Ib_Real (a / b))))

  | _, _, _ => None
  end.


Definition str_binop_sem
  (op : str_binop) (v1 v2 : I_e) : option I_e :=
  match op, v1, v2 with
  | BConcat, Ie_Single (Ih_Basic (Ib_String a)), Ie_Single (Ih_Basic (Ib_String b)) =>
      Some (Ie_Single (Ih_Basic (Ib_String (a ++ b))))
  | _, _, _ => None
  end.


Definition agg_binop_sem
  (op : agg_binop) (v1 v2 : I_e) : option I_e :=
  match op, v1, v2 with
  | BMax, Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Int b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Int (Z.max a b))))

  | BMax, Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Real b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Real (Rmax a b))))

  | BMin, Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Int b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Int (Z.min a b))))

  | BMin, Ie_Single (Ih_Basic (Ib_Real a)), Ie_Single (Ih_Basic (Ib_Real b)) =>
      Some (Ie_Single (Ih_Basic (Ib_Real (Rmin a b))))

  | BMod, Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Int b)) =>
      if Z.eqb b 0 then None
      else Some (Ie_Single (Ih_Basic (Ib_Int (Z.modulo a b))))

  | BDivInt, Ie_Single (Ih_Basic (Ib_Int a)), Ie_Single (Ih_Basic (Ib_Int b)) =>
      if Z.eqb b 0 then None
      else Some (Ie_Single (Ih_Basic (Ib_Int (a / b)%Z)))

  | _, _, _ => None
  end.




Definition binop_sem (op : binop) (v1 v2 : I_e) : option I_e :=
  match op with
  | B_Bool  o => bool_binop_sem  o v1 v2
  | B_Comp  o => comp_binop_sem  o v1 v2
  | B_Arith o => arith_binop_sem o v1 v2
  | B_Str   o => str_binop_sem   o v1 v2
  | B_Agg   o => agg_binop_sem   o v1 v2
  end.








Definition Ie_eqb (v1 v2 : I_h) : bool :=
  match v1, v2 with
  | Ih_Basic (Ib_Bool b1),   Ih_Basic (Ib_Bool b2)   => Bool.eqb b1 b2
  | Ih_Basic (Ib_Int z1),    Ih_Basic (Ib_Int z2)    => Z.eqb z1 z2
  | Ih_Basic (Ib_Real r1),   Ih_Basic (Ib_Real r2)   => Reqb r1 r2
  | Ih_Basic (Ib_String s1), Ih_Basic (Ib_String s2) => String.eqb s1 s2
  | Ih_Object c1 o1, Ih_Object c2 o2 => andb (String.eqb c1 c2) (String.eqb o1 o2)

  | _, _ => false
  end.


Definition bag_union (xs ys : list I_h) : list I_h :=
  List.app xs ys.

Definition bag_difference (xs ys : list I_h) : list I_h :=
  filter (fun x => negb (existsb (Ie_eqb x) ys)) xs.







Fixpoint all_int (xs : list I_h) : option (list Z) :=
  match xs with
  | [] => Some []
  | Ih_Basic (Ib_Int z) :: tl =>
      match all_int tl with
      | Some zs => Some (z :: zs)
      | None => None
      end
  | _ => None
  end.

Fixpoint all_real (xs : list I_h) : option (list R) :=
  match xs with
  | [] => Some []
  | Ih_Basic (Ib_Real r) :: tl =>
      match all_real tl with
      | Some rs => Some (r :: rs)
      | None => None
      end
  | _ => None
  end.


Definition aggop_sem (op : aggop) (xs : list I_h) : option I_e :=
  match op with
  | AggSize =>
      Some (Ie_Single (Ih_Basic (Ib_Int (Z.of_nat (length xs)))))

  | AggMin =>
      match all_int xs with
      | Some (z :: zs) => Some (Ie_Single (Ih_Basic (Ib_Int (fold_left Z.min zs z))))
      | Some [] => None
      | None =>
          match all_real xs with
          | Some (r :: rs) => Some (Ie_Single (Ih_Basic (Ib_Real (fold_left Rmin rs r))))
          | Some [] => None
          | None => None
          end
      end

  | AggMax =>
      match all_int xs with
      | Some (z :: zs) => Some (Ie_Single (Ih_Basic (Ib_Int (fold_left Z.max zs z))))
      | Some [] => None
      | None =>
          match all_real xs with
          | Some (r :: rs) => Some (Ie_Single (Ih_Basic (Ib_Real (fold_left Rmax rs r))))
          | Some [] => None
          | None => None
          end
      end

  | AggSum =>
      match all_int xs with
      | Some (z :: zs) => Some (Ie_Single (Ih_Basic (Ib_Int (fold_left Z.add zs 0%Z))))
      | Some [] => None
      | None =>
          match all_real xs with
          | Some rs => Some (Ie_Single (Ih_Basic (Ib_Real (fold_left Rplus rs 0%R))))
          | None => None
          end
      end

  end.


(* Inductive StringAt : string -> Z -> string -> Prop :=
  | StringAt_intro :
      forall c s i,
        (i = 1)%Z ->
        StringAt (String c s) i (String c EmptyString)
  
  | StringAt_next :
      forall c s i r,
        (i > 1)%Z ->
        StringAt s (i - 1) r ->
        StringAt (String c s) i r.


Inductive StringSub : string -> Z -> Z -> string -> Prop :=
  | StringSub_intro :
      forall s i j r,
        (i <= j)%Z ->
        StringAt s i r ->
        (* r 的长度 = j - i + 1 *)
        (* 这里可以用辅助关系 LengthString *)
        StringSub s i j r. *)



Definition dep := (var_name * I_h)%type.

(* var_binding *)
(* 表示得到这个变量的取值需要根据依赖变量的值 *)
Record var_b : Type := {
  var_val  : I_h;
  var_deps : list dep
}.

(* 一个var   ->    var的值， var依赖的var和值 *)
(* var name -> (val, [(var, val),(var, val), ... , (var, val)] ) *)
Definition env := partial_map var_b.


(* val_binding *)
(* 一个val的值， val依赖的var和值。表示得到这个val需要根据依赖var的值 *)
(* (val, [(var, val),(var, val), ... , (var, val)] ) *)
Record val_b : Type := {
  val_val  : I_e;
  val_deps : list dep
}.
        




Definition dep_eqb (d1 d2 : dep) : bool :=
  let '(x1, v1) := d1 in
  let '(x2, v2) := d2 in
  String.eqb x1 x2 && Ie_eqb v1 v2.



Fixpoint dep_in (d : dep) (ds : list dep) : bool :=
  match ds with
  | [] => false
  | d' :: tl => if dep_eqb d d' then true else dep_in d tl
  end.



Fixpoint dep_union (ds1 ds2 : list dep) : list dep :=
  match ds2 with
  | [] => ds1
  | d :: tl =>
      if dep_in d ds1
      then dep_union ds1 tl
      else dep_union (d :: ds1) tl
  end.




Inductive coerce_basic : T_b -> I_h -> I_h -> Prop :=
| Coerce_Bool :
    forall b,
      coerce_basic Tb_Bool (Ih_Basic (Ib_Bool b)) (Ih_Basic (Ib_Bool b))
| Coerce_Int :
    forall z,
      coerce_basic Tb_Int (Ih_Basic (Ib_Int z)) (Ih_Basic (Ib_Int z))
| Coerce_Real :
    forall r,
      coerce_basic Tb_Real (Ih_Basic (Ib_Real r)) (Ih_Basic (Ib_Real r))
| Coerce_String :
    forall s,
      coerce_basic Tb_String (Ih_Basic (Ib_String s)) (Ih_Basic (Ib_String s)).



Definition mk_var_b (ih : I_h) (deps : list dep) : var_b :=
  {| var_val := ih; var_deps := deps |}.








Definition option_bind {A B} (oa : option A) (k : A -> option B) : option B :=
  match oa with
  | Some a => k a
  | None => None
  end.





Fixpoint selectF
  (M : object_model)
  (SS : system_state M)
  (eval : env -> tm -> option val_b)
  (E : env)
  (var : string)
  (body : tm)
  (Th : T_h)
  (deps : list dep)
  (xs : list I_h)
  : option (list I_h) :=
  match xs with
  | [] => Some []
  | ih :: tl =>
      match eval (update E var (mk_var_b ih deps)) body with
      | None => None
      | Some vb =>
          match val_val vb with
          | Ie_Single (Ih_Basic (Ib_Bool true)) =>
              option_map (fun out_tl => ih :: out_tl)
                (selectF M SS eval E var body Th deps tl)
          | Ie_Single (Ih_Basic (Ib_Bool false)) =>
              selectF M SS eval E var body Th deps tl
          | _ => None
          end
      end
  end.



(* --------- Select 的函数语义 --------- *)

Fixpoint  cevalF
  (M : object_model)
  (SS : system_state M)
  (E : env)
  (t : tm)
  : option val_b :=
  match t with
  | CVar x =>
      match E x with
      | Some vb =>
          Some {|
            val_val  := Ie_Single (var_val vb);
            val_deps := (x, var_val vb) :: var_deps vb
          |}
      | None => None
      end

  | CLit v =>
      Some {| val_val := Ie_Single (Ih_Basic v); val_deps := [] |}

  | CUnop op t1 =>
      option_bind (cevalF M SS E t1) (fun vb =>
      option_bind (unop_sem op (val_val vb)) (fun v' =>
        Some {| val_val := v'; val_deps := val_deps vb |}))

  | CBinop op t1 t2 =>
      option_bind (cevalF M SS E t1) (fun vb1 =>
      option_bind (cevalF M SS E t2) (fun vb2 =>
      option_bind (binop_sem op (val_val vb1) (val_val vb2)) (fun v' =>
        Some {| val_val := v';
                val_deps := dep_union (val_deps vb1) (val_deps vb2) |})))

  | CAllInstances C =>
      match (sigma_CLASS M SS) C with
      | Some oids =>
          Some {|
            val_val  := Ie_Bag (Th_Object C) (map (fun oid => Ih_Object C oid) oids);
            val_deps := []
          |}
      | None => None
      end

  | CAttr t0 attr =>
      option_bind (cevalF M SS E t0) (fun vb =>
      match val_val vb with
      | Ie_Single (Ih_Object C oid) =>
          match (sigma_ATT M SS) C oid attr with
          | Some vb' =>
              Some {| val_val := Ie_Single (Ih_Basic vb');
                      val_deps := val_deps vb |}
          | None => None
          end
      | _ => None
      end)

  | CRole t0 role =>
      option_bind (cevalF M SS E t0) (fun vb =>
      match val_val vb with
      | Ie_Single (Ih_Object C oid) =>
          match lookup_nav_multiplicity M C role with
          | Some One =>
              match navigate_role M SS C oid role with
              | Some (C', [r_oid]) =>
                  Some {| val_val := Ie_Single (Ih_Object C' r_oid);
                          val_deps := val_deps vb |}
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end)

  | CNRole t0 nrole =>
      option_bind (cevalF M SS E t0) (fun vb =>
      match val_val vb with
      | Ie_Single (Ih_Object C oid) =>
          match lookup_nav_multiplicity M C nrole with
          | Some Many =>
              match navigate_role M SS C oid nrole with
              | Some (C', oids) =>
                  Some {| val_val := Ie_Bag (Th_Object C') (map (fun oid => Ih_Object C' oid) oids);
                          val_deps := val_deps vb |}
              | None => None
              end
          | _ => None
          end
      | _ => None
      end)

  | CBagLiteral Tb vs =>
      Some {| val_val := Ie_Bag (Th_Basic Tb) (map (fun ib => Ih_Basic ib) vs);
              val_deps := [] |}

  | CUnion t1 t2 =>
      option_bind (cevalF M SS E t1) (fun v1 =>
      option_bind (cevalF M SS E t2) (fun v2 =>
      match val_val v1, val_val v2 with
      | Ie_Bag Th xs, Ie_Bag Th' ys =>
          (* 你的关系语义要求同一个 Th；函数语义这里也保持一致 *)
          if (* 你若有 Th_eqb/decEq，可在这里检查；没有就用 match+refl 约束 *)
             true
          then Some {| val_val := Ie_Bag Th (bag_union xs ys);
                       val_deps := dep_union (val_deps v1) (val_deps v2) |}
          else None
      | _, _ => None
      end))

  | CDifference t1 t2 =>
      option_bind (cevalF M SS E t1) (fun v1 =>
      option_bind (cevalF M SS E t2) (fun v2 =>
      match val_val v1, val_val v2 with
      | Ie_Bag Th xs, Ie_Bag Th' ys =>
          if true
          then Some {| val_val := Ie_Bag Th (bag_difference xs ys);
                       val_deps := dep_union (val_deps v1) (val_deps v2) |}
          else None
      | _, _ => None
      end))

  | CAggregate op t0 =>
      option_bind (cevalF M SS E t0) (fun v =>
      match val_val v with
      | Ie_Bag Th xs =>
          option_bind (aggop_sem op xs) (fun v' =>
            Some {| val_val := v'; val_deps := val_deps v |})
      | _ => None
      end)



  | CSelect t0 var body =>
      option_bind (cevalF M SS E t0) (fun vb =>
      match val_val vb with
      | Ie_Bag Th xs =>
          option_bind
            (selectF M SS (fun E' t' => cevalF M SS E' t')
               E var body Th (val_deps vb) xs)
            (fun out =>
               Some {| val_val := Ie_Bag Th out;
                       val_deps := val_deps vb |})
      | _ => None
      end)



  end.








(* 
Inductive cevalR (M : object_model) : system_state M -> env -> tm -> val_b -> Prop :=


    (* ======================== Var 表达式 ======================== *)

    (* 求值规则：
          从env中取出var的值和其依赖变量列表，
          构造一个val_b，值为变量的值，依赖变量列表为var的依赖变量列表 
    *)
    | E_CVar :
        forall SS E var vb,
          E var = Some vb ->
          cevalR M SS E (CVar var) 
            {|  val_val  := Ie_Single (var_val vb); 
                val_deps := (var,  (var_val vb)) :: (var_deps vb) |}



    (* ======================== operation 表达式 ======================== *)

    (*  无参operation： 字面量构造器  *)
    (* 求值规则：
          直接构造一个val_b，值为字面量对应的I_e，依赖变量列表为空
    *)

      | E_CLit :
          forall SS E v,
            cevalR M SS E (CLit v) 
              {|  val_val  := Ie_Single (Ih_Basic v); 
                  val_deps := [] |}



    (*  basic type 有参operation： 一元操作  *)
    (* 求值规则：
          先求出子表达式的值和依赖变量列表，
          根据子表达式的值和操作符计算出结果值，
          构造一个val_b，值为结果值，依赖变量列表为子表达式的依赖变量列表
    *)
    | E_CUnop :
        forall SS E op t vb v',
          cevalR M SS E t vb ->
          unop_sem op (val_val vb) = Some v' ->
          cevalR M SS E (CUnop op t) 
              {|  val_val  := v';
                  val_deps := (val_deps vb) |}



                  

    (*  basic type 有参operation： 二元操作  *)
    | E_CBinop :
        forall SS E op t1 t2 vb1 vb2 v',
          cevalR M SS E t1 vb1 ->
          cevalR M SS E t2 vb2 ->
          binop_sem op (val_val vb1) (val_val vb2) = Some v' ->
          cevalR M SS E (CBinop op t1 t2)
              {|  val_val  := v';
                  val_deps := dep_union (val_deps vb1) (val_deps vb2) |}






    (*  object type 有参operation： allInstances, 对象属性/角色  *)
    
    (*  allInstances  *)
    (* 求值规则：
        直接从system_state_data中取出对应类的所有对象ID，
        构造一个val_b，值为包含所有对象的Bag，依赖变量列表为空
    *)
    | E_CAllInstances :
        forall SS E C oids ,
          (sigma_CLASS M SS) C = Some oids ->
          cevalR M SS E (CAllInstances C) 
            {|  val_val  := Ie_Bag (Th_Object C) (map (fun oid => Ih_Object C oid) oids);
                val_deps := [] |}



    (*  对象 / 属性 / 角色  *)
    (* 求值规则：
        先求出子表达式的值和依赖变量列表，
        根据子表达式的值（对象ID）和属性名，从system_state_data中取出对应属性值，
        构造一个val_b，值为属性值，依赖变量列表为子表达式的依赖变量列表
    *)
    | E_CAttr :
        forall SS E t oid attr v vb' C,
          cevalR M SS E t v ->
          val_val v = Ie_Single (Ih_Object C oid) ->
          (sigma_ATT M SS) C oid attr = Some vb' ->
          cevalR M SS E (CAttr t attr) 
            {|  val_val  := Ie_Single (Ih_Basic vb');
                val_deps := val_deps v |}

    (* 求值规则：
        先求出子表达式的值和依赖变量列表，
        根据子表达式的值（对象ID）和角色名，从system_state_data中取出对应关联对象ID列表，
        构造一个val_b，值为关联对象ID列表，依赖变量列表为子表达式的依赖变量列表
    *)
    | E_CRole :
        forall SS E t v C oid role C' r_oid,
          cevalR M SS E t v ->
          val_val v = Ie_Single (Ih_Object C oid) ->
          lookup_nav_multiplicity M C role = Some One ->
          navigate_role M SS C oid role = Some (C', [r_oid]) ->
          cevalR M SS E (CRole t role)
            {| val_val  := Ie_Single (Ih_Object C' r_oid);
              val_deps := val_deps v |}


    | E_CNRole :
        forall SS E t v C oid nrole C' oids,
          cevalR M SS E t v ->
          val_val v = Ie_Single (Ih_Object C oid) ->
          lookup_nav_multiplicity M C nrole = Some Many ->
          navigate_role M SS C oid nrole = Some (C', oids) ->
          cevalR M SS E (CNRole t nrole)
            {| val_val  := Ie_Bag (Th_Object C') (map (fun oid => Ih_Object C' oid) oids);
              val_deps := val_deps v |}







    (*  Bag type 有参operation： 字面量构造器 *)
    (*  集合（Bag） *)
    (* 求值规则：
        直接构造一个空的Bag，值为包含空列表的Ie_Bag，依赖变量列表为空
    *)
    | E_CBagLiteral :
        forall SS E Tb vs,
          cevalR M SS E (CBagLiteral Tb vs)
            {| val_val  := Ie_Bag (Th_Basic Tb) (map (fun ib => Ih_Basic ib) vs);
              val_deps := [] |}




    (*  Bag type 有参operation： Bag 集合运算  *)

    (*  Bag 运算  *)
    (* 求值规则：
        先求出两个子表达式的值和依赖变量列表，
        根据两个子表达式的值进行对应的Bag运算，
        构造一个val_b，值为运算结果Bag，依赖变量列表为两个子表达式的依赖变量列表的并集
    *)
    | E_CUnion :
        forall SS E t1 t2 Th v1 v2 xs ys,
          cevalR M SS E t1 v1 ->
          cevalR M SS E t2 v2 ->
          val_val v1 = Ie_Bag Th xs ->
          val_val v2 = Ie_Bag Th ys ->
          cevalR M SS E (CUnion t1 t2) 
            {|  val_val  := Ie_Bag Th (bag_union xs ys);
                val_deps := dep_union (val_deps v1) (val_deps v2) |}


    | E_CDifference :
        forall SS E t1 t2 Th v1 v2 xs ys,
          cevalR M SS E t1 v1 ->
          cevalR M SS E t2 v2 ->
          val_val v1 = Ie_Bag Th xs ->
          val_val v2 = Ie_Bag Th ys ->
          cevalR M SS E (CDifference t1 t2)
            {|  val_val  := Ie_Bag Th (bag_difference xs ys);
                val_deps := dep_union (val_deps v1) (val_deps v2) |}






    (*  bag聚合  *)
    (* 求值规则：
        先求出子表达式的值和依赖变量列表，
        根据子表达式的值进行对应的聚合计算，
        构造一个val_b，值为聚合结果，依赖变量列表为子表达式的依赖变量列表
    *)
    | E_EAggregate :
        forall SS E t Th v v' xs op,
          cevalR M SS E t v ->
          val_val v = Ie_Bag Th xs ->
          aggop_sem op xs = Some v' -> 
          cevalR M SS E (CAggregate op t)
            {|  val_val  := v';
                val_deps := val_deps v |}



    (* ======================== iterator 表达式 ======================== *)

    
    (*  Iterator（绑定变量！）, forall，exists中的varList是语法糖，可脱糖为单变量表示 *)
    (* forAll, exists, reject, one都可用select+size操作表示*)
    | E_CSelect :
        forall SS E t Th xs deps var body out,
          cevalR M SS E t {| val_val := Ie_Bag Th xs; val_deps := deps |} ->
          E_Select M SS E var body
            {| val_val := Ie_Bag Th xs;  val_deps := deps |}
            {| val_val := Ie_Bag Th out; val_deps := deps |} ->
          cevalR M SS E (CSelect t var body)
            {| val_val := Ie_Bag Th out; val_deps := deps |}




    with E_Select (M : object_model) : system_state M -> env -> string -> tm ->
          val_b -> val_b -> Prop :=

        | E_SelectNil :
            forall SS E var body Th deps,
              E_Select M SS E var body 
                {| val_val  := Ie_Bag Th [];
                   val_deps := deps |}
                {| val_val  := Ie_Bag Th [];
                   val_deps := deps |}

        | E_SelectConsKeep :
            forall SS E var body ih deps vb Th tl out_tl,
              cevalR M SS (update E var (mk_var_b ih deps)) body vb ->
              val_val vb = Ie_Single (Ih_Basic (Ib_Bool true)) ->
              E_Select M SS E var body 
                {| val_val  := Ie_Bag Th tl;
                   val_deps := deps |}
                {| val_val  := Ie_Bag Th out_tl;
                   val_deps := deps |} ->
              E_Select M SS E var body
                {| val_val  := Ie_Bag Th (ih :: tl);
                   val_deps := deps |}
                {| val_val  := Ie_Bag Th (ih :: out_tl);
                   val_deps := deps |}


        | E_SelectConsDrop :
            forall SS E var body ih deps vb Th tl out_tl,
              cevalR M SS (update E var (mk_var_b ih deps)) body vb ->
              val_val vb = Ie_Single (Ih_Basic (Ib_Bool false)) ->
              E_Select M SS E var body 
                {| val_val  := Ie_Bag Th tl;
                   val_deps := deps |}
                {| val_val  := Ie_Bag Th out_tl;
                   val_deps := deps |} ->
              E_Select M SS E var body
                {| val_val  := Ie_Bag Th (ih :: tl);
                   val_deps := deps |}
                {| val_val  := Ie_Bag Th out_tl;
                   val_deps := deps |}

              
. *)









