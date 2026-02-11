
From Stdlib Require Import String ZArith Reals List.
Import ListNotations.

From OCL.equivalence Require Import OCLSyntax Utils Models.
Open Scope string_scope.

(* ================================= Operational Semantics ======================================= *)



Definition T_b_eqb (t1 t2 : T_b) : bool :=
  match t1, t2 with
  | Tb_Bool, Tb_Bool => true
  | Tb_Int, Tb_Int => true
  | Tb_Real, Tb_Real => true
  | Tb_String, Tb_String => true
  | _, _ => false
  end.

Definition T_h_eqb (t1 t2 : T_h) : bool :=
  match t1, t2 with
  | Th_Basic b1, Th_Basic b2 => T_b_eqb b1 b2
  | Th_Object c1, Th_Object c2 => String.eqb c1 c2
  | _, _ => false
  end.




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






(* 一个var   ->    var的值， var依赖的var和值 *)
(* var name -> (val, [(var, val),(var, val), ... , (var, val)] ) *)
Definition env := partial_map I_h.







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








Definition option_bind {A B} (oa : option A) (k : A -> option B) : option B :=
  match oa with
  | Some a => k a
  | None => None
  end.






Fixpoint selectF
  (M : object_model)
  (SS : system_state M)
  (eval : env -> tm -> option I_e)
  (E : env)
  (var : string)
  (body : tm)
  (Th : T_h)
  (xs : list I_h)
  : option (list I_h) :=
  match xs with
  | [] => Some []
  | ih :: tl =>
      match eval (update E var ih) body with
      | Some (Ie_Single ih) =>
          match ih with
          | Ih_Basic (Ib_Bool true) =>
              option_map (fun out_tl => ih :: out_tl)
                (selectF M SS eval E var body Th tl)
          | Ih_Basic (Ib_Bool false) =>
              selectF M SS eval E var body Th tl
          | _ => None
          end
      | _ => None
      end
  end.


(* --------- Select 的函数语义 --------- *)

Fixpoint  cevalF
  (M : object_model)
  (SS : system_state M)
  (E : env)
  (t : tm)
  : option I_e :=
  match t with
  | CVar x =>
      match E x with
      | Some ih => Some (Ie_Single ih)
      | None => None
      end

  | CLit v => Some (Ie_Single (Ih_Basic v))

  | CUnop op t1 =>
      option_bind (cevalF M SS E t1) (fun ie =>
      option_bind (unop_sem op ie) (fun v' =>  Some v'))

  | CBinop op t1 t2 =>
      option_bind (cevalF M SS E t1) (fun ie1 =>
      option_bind (cevalF M SS E t2) (fun ie2 =>
      option_bind (binop_sem op ie1 ie2) (fun v' => Some v')))


  | CAllInstances C =>
      match (sigma_CLASS M SS) C with
      | Some oids => Some (Ie_Bag (Th_Object C) (map (fun oid => Ih_Object C oid) oids))

      | None => None
      end

  | CAttr t0 attr =>
      option_bind (cevalF M SS E t0) (fun ie =>
      match ie with
      | Ie_Single (Ih_Object C oid) =>
          match (sigma_ATT M SS) C oid attr with
          | Some ie' => Some (Ie_Single (Ih_Basic ie'))
          | None => None
          end
      | _ => None
      end)

  | CRole t0 role =>
      option_bind (cevalF M SS E t0) (fun ie =>
      match ie with
      | Ie_Single (Ih_Object C oid) =>
          match lookup_nav_multiplicity M C role with
          | Some One =>
              match navigate_role M SS C oid role with
              | Some (C', [r_oid]) => Some (Ie_Single (Ih_Object C' r_oid))
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end)

  | CNRole t0 nrole =>
      option_bind (cevalF M SS E t0) (fun ie =>
      match ie with
      | Ie_Single (Ih_Object C oid) =>
          match lookup_nav_multiplicity M C nrole with
          | Some Many =>
              match navigate_role M SS C oid nrole with
              | Some (C', oids) => Some (Ie_Bag (Th_Object C') (map (fun oid => Ih_Object C' oid) oids))
              | None => None
              end
          | _ => None
          end
      | _ => None
      end)

  | CBagLiteral Tb ie => Some (Ie_Bag (Th_Basic Tb) (map (fun ib => Ih_Basic ib) ie))


  | CUnion t1 t2 =>
      option_bind (cevalF M SS E t1) (fun ie1 =>
      option_bind (cevalF M SS E t2) (fun ie2 =>
      match ie1, ie2 with
      | Ie_Bag Th xs, Ie_Bag Th' ys =>
          (* 你的关系语义要求同一个 Th；函数语义这里也保持一致 *)
          if (* 你若有 Th_eqb/decEq，可在这里检查；没有就用 match+refl 约束 *)
             T_h_eqb Th Th'
          then Some (Ie_Bag Th (bag_union xs ys))
          else None
      | _, _ => None
      end))

  | CDifference t1 t2 =>
      option_bind (cevalF M SS E t1) (fun ie1 =>
      option_bind (cevalF M SS E t2) (fun ie2 =>
      match ie1, ie2 with
      | Ie_Bag Th xs, Ie_Bag Th' ys =>
          if T_h_eqb Th Th'
          then Some (Ie_Bag Th (bag_difference xs ys))
          else None
      | _, _ => None
      end))

  | CAggregate op t0 =>
      option_bind (cevalF M SS E t0) (fun ie =>
      match ie with
      | Ie_Bag Th xs =>
          option_bind (aggop_sem op xs) (fun v' => Some v')
      | _ => None
      end)



  | CSelect t0 var body =>
      option_bind (cevalF M SS E t0) (fun ie =>
      match ie with
      | Ie_Bag Th xs =>
          option_bind
            (selectF M SS (fun E' t' => cevalF M SS E' t')
               E var body Th xs)
            (fun out => Some (Ie_Bag Th out))
      | _ => None
      end)



  end.











