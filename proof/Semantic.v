
From Stdlib Require Import String ZArith Reals List.
Import ListNotations.

From OCL Require Import Types Syntax Utils.
Open Scope string_scope.

(* ================================= Operational Semantics ======================================= *)





Inductive value : Type :=
  | V_Bool      : bool -> value
  | V_Int       : Z -> value
  | V_Real      : R -> value
  | V_String    : string -> value
  | V_Object    : string -> value
  | V_Bag       : list value -> value.


Record obj := {
  oid   : string;             (* object identity *)
  cname  : class;              (* object's class name *)
  attrs : total_map value;   (* attribute map *)
  roles : total_map string;  (* association role -> list of target object IDs *)
  nroles : total_map (list string);  (* association role -> list of target object IDs *)
}.

Record obj_model := {
  objects : total_map obj;   (* object id -> object *)
  cmap : total_map (list string);
}.


Definition env := total_map value.     (* var name -> valu *)




Definition bool_unop_sem (op : bool_unop) (v : value) : option value :=
  match op, v with
  | UNot, V_Bool b => Some (V_Bool (negb b))
  | _, _ => None
  end.


Definition arith_unop_sem (op : arith_unop) (v : value) : option value :=
  match op, v with
  | UNeg,   V_Int n  => Some (V_Int (-n))
  | UAbs,   V_Int n  => Some (V_Int (Z.abs n))

  | UNeg,   V_Real r => Some (V_Real (-r))
  | UAbs,   V_Real r => Some (V_Real (Rabs r))

  | _, _ => None
  end.


Definition str_unop_sem (op : str_unop) (v : value) : option value :=
  match op, v with
  | UToUpper, V_String s => Some (V_String (toUpper s))
  | UToLower, V_String s => Some (V_String (toLower s))
  | _, _ => None
  end.



Definition bool_binop_sem (op : bool_binop) (b1 b2 : bool) : bool :=
  match op with
  | BAnd      => andb b1 b2
  | BOr       => orb b1 b2
  | BXor      => xorb b1 b2
  | BImplies  => orb (negb b1) b2
  end.



Definition comp_eq_sem (v1 v2 : value) : option bool :=
  match v1, v2 with
  | V_Int a, V_Int b        => Some (a =? b)%Z
  | V_Int a, V_Real b      => Some (Reqb (IZR a) b)
  | V_Real a, V_Int b      => Some (Reqb a (IZR b))
  | V_Real a, V_Real b     => Some (Reqb a b)
  | V_String a, V_String b => Some (String.eqb a b)
  | V_Object a, V_Object b => Some (String.eqb a b)
  | _, _ => None
  end.


Definition comp_lt_sem (v1 v2 : value) : option bool :=
  match v1, v2 with
  | V_Int a, V_Int b    => Some (a <? b)%Z
  | V_Int a, V_Real b  => Some (Rltb (IZR a) b)
  | V_Real a, V_Int b  => Some (Rltb a (IZR b))
  | V_Real a, V_Real b => Some (Rltb a b)
  | _, _ => None
  end.

Definition comp_le_sem (v1 v2 : value) : option bool :=
  match v1, v2 with
  | V_Int a, V_Int b    => Some (a <=? b)%Z
  | V_Int a, V_Real b  => Some (Rleb (IZR a) b)
  | V_Real a, V_Int b  => Some (Rleb a (IZR b))
  | V_Real a, V_Real b => Some (Rleb a b)
  | _, _ => None
  end.


Definition comp_binop_sem
  (op : comp_binop) (v1 v2 : value) : option bool :=
  match op with
  | BEq => comp_eq_sem v1 v2
  | BNe => option_map negb (comp_eq_sem v1 v2)
  | BLt => comp_lt_sem v1 v2
  | BLe => comp_le_sem v1 v2
  | BGt => option_map negb (comp_le_sem v1 v2)
  | BGe => option_map negb (comp_lt_sem v1 v2)
  end.



Definition arith_binop_sem
  (op : arith_binop) (v1 v2 : value) : option value :=
  match op, v1, v2 with
  | BAdd, V_Int a, V_Int b =>
      Some (V_Int (a + b)%Z)

  | BAdd, V_Int a, V_Real b =>
      Some (V_Real (IZR a + b))

  | BAdd, V_Real a, V_Int b =>
      Some (V_Real (a + IZR b))

  | BAdd, V_Real a, V_Real b =>
      Some (V_Real (a + b))

  | BSub, V_Int a, V_Int b =>
      Some (V_Int (a - b)%Z)

  | BSub, V_Int a, V_Real b =>
      Some (V_Real (IZR a - b))

  | BSub, V_Real a, V_Int b =>
      Some (V_Real (a - IZR b))

  | BSub, V_Real a, V_Real b =>
      Some (V_Real (a - b))

  | BMul, V_Int a, V_Int b =>
      Some (V_Int (a * b)%Z)

  | BMul, V_Int a, V_Real b =>
      Some (V_Real (IZR a * b))

  | BMul, V_Real a, V_Int b =>
      Some (V_Real (a * IZR b))

  | BMul, V_Real a, V_Real b =>
      Some (V_Real (a * b))

  | BDiv, V_Int a, V_Int b =>
      if Z.eqb b 0 then None
      else Some (V_Real (IZR a / IZR b))

  | BDiv, V_Int a, V_Real b =>
      if Reqb b 0 then None
      else Some (V_Real (IZR a / b))

  | BDiv, V_Real a, V_Int b =>
      if Z.eqb b 0 then None
      else Some (V_Real (a / IZR b))

  | BDiv, V_Real a, V_Real b =>
      if Reqb b 0 then None
      else Some (V_Real (a / b))

  | _, _, _ => None
  end.


Definition str_binop_sem
  (op : str_binop) (v1 v2 : value) : option value :=
  match op, v1, v2 with
  | BConcat, V_String a, V_String b =>
      Some (V_String (a ++ b))
  | _, _, _ => None
  end.


Definition agg_binop_sem
  (op : agg_binop) (v1 v2 : value) : option value :=
  match op, v1, v2 with
  | BMax, V_Int a, V_Int b =>
      Some (V_Int (Z.max a b))

  | BMax, V_Real a, V_Real b =>
      Some (V_Real (Rmax a b))

  | BMin, V_Int a, V_Int b =>
      Some (V_Int (Z.min a b))

  | BMin, V_Real a, V_Real b =>
      Some (V_Real (Rmin a b))

  | BMod, V_Int a, V_Int b =>
      if Z.eqb b 0 then None
      else Some (V_Int (Z.modulo a b))

  | BDivInt, V_Int a, V_Int b =>
      if Z.eqb b 0 then None
      else Some (V_Int (a / b)%Z)

  | _, _, _ => None
  end.





Definition value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | V_Bool b1,   V_Bool b2   => Bool.eqb b1 b2
  | V_Int z1,    V_Int z2    => Z.eqb z1 z2
  | V_String s1, V_String s2 => String.eqb s1 s2
  | V_Object o1, V_Object o2 => String.eqb o1 o2
  (*| V_Bag xs,    V_Bag ys    =>
      list_value_eqb xs ys   (* 可选，见下 *) *)
  | _, _ => false
  end.


Definition bag_union (xs ys : list value) : list value :=
  xs ++ ys.

Definition bag_intersect (xs ys : list value) : list value :=
  filter (fun x => existsb (value_eqb x) ys) xs.

Definition bag_difference (xs ys : list value) : list value :=
  filter (fun x => negb (existsb (value_eqb x) ys)) xs.

Definition bag_symdiff (xs ys : list value) : list value :=
  bag_union (bag_difference xs ys) (bag_difference ys xs).




Definition bag_includes (xs ys : list value) : bool :=
  existsb (fun x => existsb (value_eqb x) xs) ys.


Definition bag_includes_all (xs ys : list value) : bool :=
  forallb (fun y => existsb (value_eqb y) xs) ys.



Definition bag_excludes (xs ys : list value) : bool :=
  negb (bag_includes xs ys).

Definition bag_excludes_all (xs ys : list value) : bool :=
  forallb (fun y => negb (existsb (value_eqb y) xs)) ys.

Definition bag_is_empty (xs : list value) : bool :=
  match xs with
  | [] => true
  | _  => false
  end.

Definition bag_not_empty (xs : list value) : bool :=
  negb (bag_is_empty xs).

Fixpoint bag_is_unique (xs : list value) : bool :=
  match xs with
  | [] => true
  | x :: xs' =>
      negb (existsb (value_eqb x) xs')
      && bag_is_unique xs'
  end.





Fixpoint all_int (xs : list value) : option (list Z) :=
  match xs with
  | [] => Some []
  | V_Int z :: tl =>
      match all_int tl with
      | Some zs => Some (z :: zs)
      | None => None
      end
  | _ => None
  end.

Fixpoint all_real (xs : list value) : option (list R) :=
  match xs with
  | [] => Some []
  | V_Real r :: tl =>
      match all_real tl with
      | Some rs => Some (r :: rs)
      | None => None
      end
  | _ => None
  end.


Definition aggop_sem (op : aggop) (xs : list value) : option value :=
  match op with
  | AggSize =>
      Some (V_Int (Z.of_nat (length xs)))

  | AggMin =>
      match all_int xs with
      | Some (z :: zs) => Some (V_Int (fold_left Z.min zs z))
    | Some [] =>
          (* 空集合：通常 undefined *)
          None
      | None =>
          match all_real xs with
          | Some (r :: rs) => Some (V_Real (fold_left Rmin rs r))
          | Some [] => None
          | None => None
          end
      end

  | AggMax =>
      match all_int xs with
      | Some (z :: zs) => Some (V_Int (fold_left Z.max zs z))
      | Some [] => None
      | None =>
          match all_real xs with
          | Some (r :: rs) => Some (V_Real (fold_left Rmax rs r))
          | Some [] => None
          | None => None
          end
      end

  | AggSum =>
      match all_int xs with
      | Some zs => Some (V_Int (fold_left Z.add zs 0%Z))
      | None =>
          match all_real xs with
          | Some rs => Some (V_Real (fold_left Rplus rs 0%R))
          | None => None
          end
      end



  (* | AggAvg =>
      (* avg 空集合通常 undefined；也可定义为 0 *)
      match all_int xs with
      | Some [] => None
      | Some zs =>
          let n := Z.of_nat (length zs) in
          if Z.eqb n 0 then None
          else Some (V_Real ((IZR (fold_left Z.add zs 0%Z)) / (IZR n))%R)
      | None =>
          match all_real xs with
          | Some [] => None
          | Some rs =>
              let n := INR (length rs) in
              (* length rs = 0 已被 [] 分支排除 *)
              Some (V_Real ((fold_left Rplus rs 0%R) / n)%R)
          | None => None
          end
      end *)
  end.


Inductive StringAt : string -> Z -> string -> Prop :=
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
        StringSub s i j r.





        

Inductive cevalR : obj_model -> env -> tm -> value -> Prop :=



  (*  字面量  *)

      | E_CBool :
          forall M E b,
            cevalR M E (CBool b) (V_Bool b)

      | E_CInt :
          forall M E n,
            cevalR M E (CInt n) (V_Int n)

      | E_CReal :
          forall M E r,
            cevalR M E (CReal r) (V_Real r)

      | E_CString :
          forall M E s,
            cevalR M E (CString s) (V_String s)

      (* | E_CObject :
          forall M E oid,
            cevalR M E (CObject oid) (V_Object oid) *)


  (*  集合（Bag） *)

      | E_CEmptyBag :
          forall M E T,
            cevalR M E (CEmptyBag T) (V_Bag [])

      | E_CBagLiteral :
          forall M E ts vs,
            E_BagLiteral M E ts vs ->
            cevalR M E (CBagLiteral ts) (V_Bag vs)




  (* context C inv body 语义：对所有实例执行 forAll *)
      | E_CContext :
          forall M E C body v,
            cevalR M E (CForAll (CAllInstances C) "self" body) v ->
            cevalR M E (CContext C body) v
      


  (* Var Self *)

      | E_CVar :
          forall M E var v,
            E var = v ->
            cevalR M E (CVar var) v
      

      | E_CSelf :
          forall M E oid,
            E "self" = V_Object oid ->
            cevalR M E CSelf (V_Object oid)



  (*  对象 / 属性 / 角色  *)

      | E_CAttr :
          forall M E t oid attr v,
            cevalR M E t (V_Object oid) ->
            attrs (objects M oid) attr = v ->
            cevalR M E (CAttr t attr) v


      | E_CRole :
          forall M E t oid role r_oid,
            cevalR M E t (V_Object oid) ->
            roles (objects M oid) role = r_oid ->
            cevalR M E (CRole t role) (V_Object r_oid)


      | E_CNRole :
          forall M E t oid nrole oids,
            cevalR M E t (V_Object oid) ->
            nroles (objects M oid) nrole = oids ->
            cevalR M E (CNRole t nrole)
                  (V_Bag (map V_Object oids))



  (*  allInstances  *)

      | E_CAllInstances :
          forall M E C oids,
            cmap M C = oids ->
            cevalR M E (CAllInstances C) (V_Bag (map V_Object oids))

        


  (* 一元运算 *)


      | E_CBoolUn :
          forall M E op t v v',
            cevalR M E t v ->
            bool_unop_sem op v = Some v' ->
            cevalR M E (CBoolUn op t) v'



      | E_CArithUn :
          forall M E op t v v',
            cevalR M E t v ->
            arith_unop_sem op v = Some v' ->
            cevalR M E (CArithUn op t) v'

      | E_CArithUnRealUFloor :
        forall M E t r z,
          cevalR M E t (V_Real r) ->
          Rfloor_real r z ->
          cevalR M E (CArithUn UFloor t) (V_Int z)

      | E_CArithUnRealURound :
        forall M E t r z,
          cevalR M E t (V_Real r) ->
          Rround_real r z ->
          cevalR M E (CArithUn URound t) (V_Int z)




      | E_CStrUn :
          forall M E op t v v',
            cevalR M E t v ->
            str_unop_sem op v = Some v' ->
            cevalR M E (CStrUn op t) v'




  (* 二元运算 *)

    (* 二元逻辑运算 *)

      | E_CBoolBin :
          forall M E op t1 t2 b1 b2,
            cevalR M E t1 (V_Bool b1) ->
            cevalR M E t2 (V_Bool b2) ->
            cevalR M E (CBoolBin op t1 t2) (V_Bool (bool_binop_sem op b1 b2))


    (* 二元比较运算 *)

      | E_CCompBin :
          forall M E op t1 t2 v1 v2 b,
            cevalR M E t1 v1 ->
            cevalR M E t2 v2 ->
            comp_binop_sem op v1 v2 = Some b ->
            cevalR M E (CCompBin op t1 t2) (V_Bool b)


    (* 二元算数运算 *)

      | E_CArithBin :
          forall M E op t1 t2 v1 v2 v,
            cevalR M E t1 v1 ->
            cevalR M E t2 v2 ->
            arith_binop_sem op v1 v2 = Some v ->
            cevalR M E (CArithBin op t1 t2) v



    (* 二元字符串运算 *)

      | E_CStrBin :
          forall M E op t1 t2 v1 v2 v,
            cevalR M E t1 v1 ->
            cevalR M E t2 v2 ->
            str_binop_sem op v1 v2 = Some v ->
            cevalR M E (CStrBin op t1 t2) v

    (* 二元聚合运算 *)

      | E_CAggBin :
          forall M E op t1 t2 v1 v2 v,
            cevalR M E t1 v1 ->
            cevalR M E t2 v2 ->
            agg_binop_sem op v1 v2 = Some v ->
            cevalR M E (CAggBin op t1 t2) v


  (*  Bag 运算  *)

      | E_CUnion :
          forall M E t1 t2 xs ys,
            cevalR M E t1 (V_Bag xs) ->
            cevalR M E t2 (V_Bag ys) ->
            cevalR M E (CUnion t1 t2) (V_Bag (bag_union xs ys))

      | E_CIntersect :
          forall M E t1 t2 xs ys,
            cevalR M E t1 (V_Bag xs) ->
            cevalR M E t2 (V_Bag ys) ->
            cevalR M E (CIntersect t1 t2) (V_Bag (bag_intersect xs ys))

      | E_CDifference :
        forall M E t1 t2 xs ys,
          cevalR M E t1 (V_Bag xs) ->
          cevalR M E t2 (V_Bag ys) ->
          cevalR M E (CDifference t1 t2) (V_Bag (bag_difference xs ys))

      | E_CSymDiff :
          forall M E t1 t2 xs ys,
            cevalR M E t1 (V_Bag xs) ->
            cevalR M E t2 (V_Bag ys) ->
            cevalR M E (CSymDiff t1 t2) (V_Bag (bag_symdiff xs ys))

  (*  Bag 谓词  *)

      | E_CIncludes :
          forall M E t1 t2 xs ys,
            cevalR M E t1 (V_Bag xs) ->
            cevalR M E t2 (V_Bag ys) ->
            cevalR M E (CIncludes t1 t2) (V_Bool (bag_includes xs ys))

      | E_CIncludesAll :
          forall M E t1 t2 xs ys,
            cevalR M E t1 (V_Bag xs) ->
            cevalR M E t2 (V_Bag ys) ->
            cevalR M E (CIncludesAll t1 t2) (V_Bool (bag_includes_all xs ys))


      | E_CExcludes :
          forall M E t1 t2 xs ys,
            cevalR M E t1 (V_Bag xs) ->
            cevalR M E t2 (V_Bag ys) ->
            cevalR M E (CExcludes t1 t2) (V_Bool (bag_excludes xs ys))

      | E_CExcludesAll :
          forall M E t1 t2 xs ys,
            cevalR M E t1 (V_Bag xs) ->
            cevalR M E t2 (V_Bag ys) ->
            cevalR M E (CExcludesAll t1 t2) (V_Bool (bag_excludes_all xs ys))

      | E_CIsEmpty :
          forall M E t xs,
            cevalR M E t (V_Bag xs) ->
            cevalR M E (CIsEmpty t) (V_Bool (bag_is_empty xs))

      | E_CNotEmpty :
          forall M E t xs,
            cevalR M E t (V_Bag xs) ->
            cevalR M E (CNotEmpty t) (V_Bool (bag_not_empty xs))


  (*  Iterator（绑定变量！）, forall，exists中的varList是语法糖，可脱糖为单变量表示 *)



      | E_CForAll :
        forall M E bag_tm var body vs b,
          cevalR M E bag_tm (V_Bag vs) ->
          E_Forall M E var body vs b ->
          cevalR M E (CForAll bag_tm var body) (V_Bool b)


      | E_CExists :
          forall M E bag_tm var body vs b,
            cevalR M E bag_tm (V_Bag vs) ->
            E_Exists M E var body vs b ->
            cevalR M E (CExists bag_tm var body) (V_Bool b)


      | E_CSelect :
          forall M E bag_tm var body vs vs',
            cevalR M E bag_tm (V_Bag vs) ->
            E_Select M E var body vs vs' ->
            cevalR M E (CSelect bag_tm var body) (V_Bag vs')


      | E_CReject :
          forall M E bag_tm var body vs vs',
            cevalR M E bag_tm (V_Bag vs) ->
            E_Reject M E var body vs vs' ->
            cevalR M E (CReject bag_tm var body) (V_Bag vs')


      | E_COne :
            forall M E bag_tm var body vs b,
              cevalR M E bag_tm (V_Bag vs) ->
              E_One M E var body vs b ->
              cevalR M E (COne bag_tm var body) (V_Bool b)



      | E_CCollect :
            forall M E bag_tm attr vs vs',
              cevalR M E bag_tm (V_Bag vs) ->
              E_Collect M E attr vs vs' ->
              cevalR M E (CCollect bag_tm attr) (V_Bag vs')



      | E_CRCollect :
            forall M E bag_tm role vs vs',
              cevalR M E bag_tm (V_Bag vs) ->
              E_RCollect M E role vs vs' ->
              cevalR M E (CRCollect bag_tm role) (V_Bag vs')


      | E_CNRCollect :
            forall M E bag_tm nrole vs vs',
              cevalR M E bag_tm (V_Bag vs) ->
              E_NRCollect M E nrole vs vs' ->
              cevalR M E (CNRCollect bag_tm nrole) (V_Bag vs')


  (*  bag聚合  *)

      | E_EAggregate :
          forall M E op t xs v,
            cevalR M E t (V_Bag xs) ->
            aggop_sem op xs = Some v -> cevalR M E (EAggregate op t) v


  (* String ops with integer arguments *)

      | E_EAt :
          forall M E t s i r,
            cevalR M E t (V_String s) ->
            StringAt s i r ->
            cevalR M E (EAt t i) (V_String r)

      | E_ESubstring :
          forall M E t s i j r,
            cevalR M E t (V_String s) ->
            StringSub s i j r ->
            cevalR M E (ESubstring t i j) (V_String r)






            

      with E_BagLiteral :
            obj_model -> env -> list tm -> list value -> Prop :=
        | E_BagLitNil :
            forall M E,
              E_BagLiteral M E [] []

        | E_BagLitCons :
            forall M E t tl v vl,
              cevalR M E t v ->
              E_BagLiteral M E tl vl ->
              E_BagLiteral M E (t :: tl) (v :: vl)  

      with E_Forall :
            obj_model -> env -> string -> tm ->
            list value -> bool -> Prop :=
      
        | E_ForallNil :
            forall M E var body,
            E_Forall M E var body [] true
        
        | E_ForallConsTrue :
            forall M E var body v tl,
              cevalR M (t_update E var v) body (V_Bool true) ->
              E_Forall M E var body tl true ->
              E_Forall M E var body (v :: tl) true
        
        | E_ForallConsFalse :
            forall M E var body v tl,
              cevalR M (t_update E var v) body (V_Bool false) ->
              E_Forall M E var body (v :: tl) false

      with E_Exists :
            obj_model -> env -> string -> tm ->
            list value -> bool -> Prop :=

        | E_ExistsNil :
            forall M E var body,
              E_Exists M E var body [] false
        
        | E_ExistsConsTrue :
            forall M E var body v tl,
              cevalR M (t_update E var v) body (V_Bool true) ->
              E_Exists M E var body (v :: tl) true
        
        | E_ExistsConsFalse :
            forall M E var body v tl,
              cevalR M (t_update E var v) body (V_Bool false) ->
              E_Exists M E var body tl true ->
              E_Exists M E var body (v :: tl) true

      with E_Select :
          obj_model -> env -> string -> tm ->
          list value -> list value -> Prop :=

        | E_SelectNil :
            forall M E var body,
              E_Select M E var body [] []

        | E_SelectConsKeep :
            forall M E var body v tl out_tl,
              cevalR M (t_update E var v) body (V_Bool true) ->
              E_Select M E var body tl out_tl ->
              E_Select M E var body (v :: tl) (v :: out_tl)

        | E_SelectConsDrop :
            forall M E var body v tl out_tl,
              cevalR M (t_update E var v) body (V_Bool false) ->
              E_Select M E var body tl out_tl ->
              E_Select M E var body (v :: tl) out_tl

      with E_Reject :
              obj_model -> env -> string -> tm ->
              list value -> list value -> Prop :=
        
        | E_RejectNil :
            forall M E var body,
              E_Reject M E var body [] []
        
        | E_RejectConsKeep :
            forall M E var body v tl out_tl,
              cevalR M (t_update E var v) body (V_Bool false) ->
              E_Reject M E var body tl out_tl ->
              E_Reject M E var body (v :: tl) (v :: out_tl)
        
        | E_RejectConsDrop :
            forall M E var body v tl out_tl,
              cevalR M (t_update E var v) body (V_Bool true) ->
              E_Reject M E var body tl out_tl ->
              E_Reject M E var body (v :: tl) out_tl
        

      with E_One :
              obj_model -> env -> string -> tm ->
              list value -> bool -> Prop :=
        
        | E_OneTrue :
            forall M E var body bag res,
              E_Select M E var body bag res ->
              length res = 1 ->
              E_One M E var body bag true
        
        | E_OneFalse :
            forall M E var body bag res,
              E_Select M E var body bag res ->
              length res <> 1 ->
              E_One M E var body bag false


      with E_Attr :
              obj_model -> value -> string -> value -> Prop :=

        | E_ObjAttr :
            forall M oid attr v,
              attrs (objects M oid) attr = v ->
              E_Attr M (V_Object oid) attr v


      with E_Collect :
              obj_model -> env -> string ->
              list value -> list value -> Prop :=
        
        | E_CollectNil :
            forall M E attr,
              E_Collect M E attr [] []
        
        | E_CollectCons :
            forall M E attr v tl v_attr out_tl,
              E_Attr M v attr v_attr ->
              E_Collect M E attr tl out_tl ->
              E_Collect M E attr (v :: tl) (v_attr :: out_tl)
            

      with E_Role :
              obj_model -> value -> string -> value -> Prop :=
        | E_ObjRole :
            forall M oid role r_oid,
              roles (objects M oid) role = r_oid ->
              E_Role M (V_Object oid) role (V_Object r_oid)


      with E_RCollect :
              obj_model -> env -> string ->
              list value -> list value -> Prop :=
        
        | E_RCollectNil :
            forall M E role,
              E_RCollect M E role [] []
        
        | E_RCollectCons :
            forall M E role v tl v' out_tl,
              E_Role M v role v' ->
              E_RCollect M E role tl out_tl ->
              E_RCollect M E role (v :: tl) (v' :: out_tl)



      with E_NRole :
              obj_model -> value -> string -> list value -> Prop :=
        | E_ObjNRole :
            forall M oid role oids,
              nroles (objects M oid) role = oids ->
              E_NRole M (V_Object oid) role (map V_Object oids)


      with E_NRCollect :
              obj_model -> env -> string ->
              list value -> list value -> Prop :=
            
        | E_NRCollectNil :
            forall M E role,
              E_NRCollect M E role [] []
        
        | E_NRCollectCons :
            forall M E role v tl vs out_tl,
              E_NRole M v role vs ->
              E_NRCollect M E role tl out_tl ->
              E_NRCollect M E role (v :: tl) (vs ++ out_tl).

