(*************************************************************)
(*                                                           *)
(*        Relational Algebra Semantics (Big-step)             *)
(*                                                           *)
(*  Design principles:                                       *)
(*  - RexNode: row-level, pure, no DB access                 *)
(*  - ra_rel  : relation-level, evaluated over DBInstance     *)
(*                                                           *)
(*************************************************************)

From Stdlib Require Import String List ZArith Reals.

Import ListNotations.
Open Scope string_scope.


From OCL.equivalence Require Import Models OCLSyntax OCLSemantic RASyntax Utils.





Definition bool_unop_sem_ra (op : bool_unop) (v : I_ra) : option I_ra :=
  match op, v with
  | UNot, Ira_Bool b => Some (Ira_Bool (negb b))
  | _, _ => None
  end.

Definition arith_unop_sem_ra (op : arith_unop) (v : I_ra) : option I_ra :=
  match op, v with
  | UNeg,   Ira_Int n  => Some (Ira_Int (-n))
  | UAbs,   Ira_Int n  => Some (Ira_Int (Z.abs n))
  | UNeg,   Ira_Real r => Some (Ira_Real (-r))
  | UAbs,   Ira_Real r => Some (Ira_Real (Rabs r))
  | UFloor, Ira_Real r => Some (Ira_Int (Int_part r))
  | URound, Ira_Real r => Some (Ira_Int (round_Z r))
  | _, _ => None
  end.



Definition str_unop_sem_ra (op : str_unop) (v : I_ra) : option I_ra :=
  match op, v with
  | UToUpper, Ira_String s => Some (Ira_String (toUpper s))
  | UToLower, Ira_String s => Some (Ira_String (toLower s))
  | USize,    Ira_String s => Some (Ira_Int (Z.of_nat (String.length s)))
  
  | _, _ => None
  end.





Definition unop_sem_ra (op : unop) (v1 : I_ra) : option I_ra :=
  match op with
  | U_Bool  o => bool_unop_sem_ra  o v1
  | U_Arith o => arith_unop_sem_ra o v1
  | U_Str   o => str_unop_sem_ra   o v1
  end.



Definition bool_binop_sem_ra (op : bool_binop) (b1 b2 : I_ra) : option I_ra :=
  match op, b1, b2 with
  | BAnd,     Ira_Bool b1,  Ira_Bool b2 => Some (Ira_Bool (andb b1 b2))
  | BOr,      Ira_Bool b1,  Ira_Bool b2 => Some (Ira_Bool (orb b1 b2))
  | BXor,     Ira_Bool b1,  Ira_Bool b2 => Some (Ira_Bool (xorb b1 b2))
  | BImplies, Ira_Bool b1,  Ira_Bool b2 => Some (Ira_Bool (orb (negb b1) b2))

  | _, _, _ => None
  end.



Definition comp_eq_sem_ra (v1 v2 : I_ra) : option bool :=
  match v1, v2 with
  | Ira_Int a, Ira_Int b        => Some (a =? b)%Z
  | Ira_Int a, Ira_Real b      => Some (Reqb (IZR a) b)
  | Ira_Real a, Ira_Int b      => Some (Reqb a (IZR b))
  | Ira_Real a, Ira_Real b     => Some (Reqb a b)
  | Ira_String a, Ira_String b => Some (String.eqb a b)
  | Ira_Object c1 d1, Ira_Object c2 d2 => Some (andb (String.eqb c1 c2) (String.eqb d1 d2))
  | _, _ => None
  end.



Definition comp_lt_sem_ra (v1 v2 : I_ra) : option bool :=
  match v1, v2 with
  | Ira_Int a, Ira_Int b        => Some (a <? b)%Z
  | Ira_Int a, Ira_Real b      => Some (Rltb (IZR a) b)
  | Ira_Real a, Ira_Int b      => Some (Rltb a (IZR b))
  | Ira_Real a, Ira_Real b     => Some (Rltb a b)
  | _, _ => None
  end.



Definition comp_le_sem_ra (v1 v2 : I_ra) : option bool :=
  match v1, v2 with
  | Ira_Int a, Ira_Int b        => Some (a <=? b)%Z
  | Ira_Int a, Ira_Real b      => Some (Rleb (IZR a) b)
  | Ira_Real a, Ira_Int b      => Some (Rleb a (IZR b))
  | Ira_Real a, Ira_Real b     => Some (Rleb a b)
  | _, _ => None
  end.



Definition lift_bool_Ie_ra (ob : option bool) : option I_ra :=
  option_map (fun b => Ira_Bool b) ob.
  
Definition comp_binop_sem_ra
  (op : comp_binop) (v1 v2 : I_ra) : option I_ra :=
  lift_bool_Ie_ra (
  match op with
  | BEq => comp_eq_sem_ra v1 v2
  | BNe => option_map negb (comp_eq_sem_ra v1 v2)
  | BLt => comp_lt_sem_ra v1 v2
  | BLe => comp_le_sem_ra v1 v2
  | BGt => comp_lt_sem_ra v2 v1
  | BGe => comp_le_sem_ra v2 v1
  end
  ).




Definition arith_binop_sem_ra
  (op : arith_binop) (v1 v2 : I_ra) : option I_ra :=
  match op, v1, v2 with
  | BAdd, Ira_Int a, Ira_Int b => Some (Ira_Int (a + b)%Z)
  | BAdd, Ira_Int a, Ira_Real b => Some (Ira_Real (IZR a + b))
  | BAdd, Ira_Real a, Ira_Int b => Some (Ira_Real (a + IZR b))
  | BAdd, Ira_Real a, Ira_Real b => Some (Ira_Real (a + b))

  | BSub,Ira_Int a, Ira_Int b => Some (Ira_Int (a - b)%Z)
  | BSub, Ira_Int a, Ira_Real b => Some (Ira_Real (IZR a - b))
  | BSub, Ira_Real a, Ira_Int b => Some (Ira_Real (a - IZR b))
  | BSub, Ira_Real a, Ira_Real b => Some (Ira_Real (a - b))

  | BMul, Ira_Int a, Ira_Int b => Some (Ira_Int (a * b)%Z)
  | BMul, Ira_Int a, Ira_Real b => Some (Ira_Real ((IZR a) * b))
  | BMul, Ira_Real a, Ira_Int b => Some (Ira_Real (a * IZR b))
  | BMul, Ira_Real a, Ira_Real b => Some (Ira_Real (a * b))

  | BDiv, Ira_Int a, Ira_Int b => if Z.eqb b 0 then None else Some (Ira_Real (IZR a / IZR b))
  | BDiv, Ira_Int a, Ira_Real b => if Reqb b 0 then None else Some (Ira_Real (IZR a / b))
  | BDiv, Ira_Real a, Ira_Int b => if Z.eqb b 0 then None else Some (Ira_Real (a / IZR b))
  | BDiv, Ira_Real a, Ira_Real b => if Reqb b 0 then None else Some (Ira_Real (a / b))

  | _, _, _ => None
  end.





Definition str_binop_sem_ra
  (op : str_binop) (v1 v2 : I_ra) : option I_ra :=
  match op, v1, v2 with
  | BConcat, Ira_String a, Ira_String b =>
      Some (Ira_String (a ++ b))
  | _, _, _ => None
  end.



Definition agg_binop_sem_ra
  (op : agg_binop) (v1 v2 : I_ra) : option I_ra :=
  match op, v1, v2 with
  | BMax, Ira_Int a, Ira_Int b =>
      Some (Ira_Int (Z.max a b))

  | BMax, Ira_Real a, Ira_Real b =>
      Some (Ira_Real (Rmax a b))

  | BMin, Ira_Int a, Ira_Int b =>
      Some (Ira_Int (Z.min a b))

  | BMin, Ira_Real a, Ira_Real b =>
      Some (Ira_Real (Rmin a b))

  | BMod, Ira_Int a, Ira_Int b =>
      if Z.eqb b 0 then None
      else Some (Ira_Int (Z.modulo a b))

  | BDivInt, Ira_Int a, Ira_Int b =>
      if Z.eqb b 0 then None
      else Some (Ira_Int (a / b)%Z)

  | _, _, _ => None
  end.




Definition binop_sem_ra (op : binop) (v1 v2 : I_ra) : option I_ra :=
  match op with
  | B_Bool  o => bool_binop_sem_ra  o v1 v2
  | B_Comp  o => comp_binop_sem_ra  o v1 v2
  | B_Arith o => arith_binop_sem_ra o v1 v2
  | B_Str   o => str_binop_sem_ra   o v1 v2
  | B_Agg   o => agg_binop_sem_ra   o v1 v2
  end.












(*************************************************************)
(*                 Row-level semantics                       *)
(*                RexNode evaluation                         *)
(*************************************************************)

(* RexNode evaluation is:
     - row-local
     - pure
     - total up to option failure
*)

(* Inductive evalRexR : RowData -> rex -> I_ra -> Prop :=

| ER_Col :
    forall row cn v,
      lookup_row cn row = Some v ->
      evalRexR row (RCol cn) v

| ER_Val :
    forall row v,
      evalRexR row (RLit v) v

| ER_Unop :
    forall row op e1 v1 v,
      evalRexR row e1 v1 ->
      unop_sem_ra op v1 = Some v ->
      evalRexR row (RUnop op e1) v



| ER_Binop :
    forall row op e1 e2 v1 v2 v,
      evalRexR row e1 v1 ->
      evalRexR row e2 v2 ->
      binop_sem_ra op v1 v2 = Some v ->
      evalRexR row (RBinop op e1 e2) v


. *)



(* Merge two rows (used by join).
   Schema disjointness is guaranteed by typing. *)
Definition row_merge (r1 r2 : RowData) : RowData :=
        List.app r1 r2.





(* 从RowData中提取列名集合 *)
Definition row_cols (r : RowData) : list ColName :=
  map fst r.

(* 判断两个 RowData 是否没有共同的列名 *)
Definition disjoint_cols (r1 r2 : RowData) : Prop :=
  forall c,
    ~ (In c (row_cols r1) /\ In c (row_cols r2)).






(*************************************************************)
(*                  Row construction helpers                 *)
(*************************************************************)




(* 值的判等 *)
Definition Ira_eq_sem (v1 v2 : I_ra) : option bool :=
  match v1, v2 with
  | Ira_Bool b1,   Ira_Bool b2   => Some (Bool.eqb b1 b2)

  | Ira_Int a,     Ira_Int b     => Some (Z.eqb a b)
  | Ira_Int a,     Ira_Real b    => Some (Reqb (IZR a) b)
  | Ira_Real a,    Ira_Int b     => Some (Reqb a (IZR b))
  | Ira_Real a,    Ira_Real b    => Some (Reqb a b)

  | Ira_String s1, Ira_String s2 => Some (String.eqb s1 s2)

  | Ira_Object c1 o1, Ira_Object c2 o2 =>
      Some (andb (String.eqb c1 c2) (String.eqb o1 o2))

  | _, _ => None
  end.


(* 把 option bool 压成 bool *)
Definition Ira_eqb (v1 v2 : I_ra) : bool :=
  match Ira_eq_sem v1 v2 with
  | Some b => b
  | None => false
  end.


(* RowData 的判等（按 list 结构逐项比较） *)
Fixpoint rowdata_eqb (r1 r2 : RowData) : bool :=
  match r1, r2 with
  | [], [] => true
  | (k1,v1)::t1, (k2,v2)::t2 =>
      andb (String.eqb k1 k2)
           (andb (Ira_eqb v1 v2) (rowdata_eqb t1 t2))
  | _, _ => false
  end.


Fixpoint row_inb (x : RowData) (ys : list RowData) : bool :=
  match ys with
  | [] => false
  | y :: ys' => if rowdata_eqb x y then true else row_inb x ys'
  end.


Fixpoint bag_diff_rows (xs ys : list RowData) : list RowData :=
  match xs with
  | [] => []
  | x :: xs' =>
      if row_inb x ys then
        bag_diff_rows xs' ys
      else
        x :: bag_diff_rows xs' ys
  end.


Fixpoint remove_dup_rows (xs : list RowData) : list RowData :=
  match xs with
  | [] => []
  | x :: xs' =>
      if row_inb x xs' then
        remove_dup_rows xs'
      else
        x :: remove_dup_rows xs'
  end.



(* 在 RowData中取出给定colname的列值*)
Fixpoint lookup_row_col (c : ColName) (r : RowData) : option I_ra :=
  match r with
  | [] => None
  | (k,v) :: tl => if String.eqb k c then Some v else lookup_row_col c tl
  end.








Fixpoint all_int_ra (xs : list I_ra) : option (list Z) :=
  match xs with
  | [] => Some []
  | Ira_Int z :: tl =>
      match all_int_ra tl with
      | Some zs => Some (z :: zs)
      | None => None
      end
  | _ :: _ => None
  end.

Fixpoint all_real_ra (xs : list I_ra) : option (list R) :=
  match xs with
  | [] => Some []
  | Ira_Real r :: tl =>
      match all_real_ra tl with
      | Some rs => Some (r :: rs)
      | None => None
      end
  | _ :: _ => None
  end.






Definition aggop_ra_sem (op : aggop) (xs : list I_ra) : option I_ra :=
  match op with
  | AggSize =>
      Some (Ira_Int (Z.of_nat (length xs)))

  | AggMin =>
      match all_int_ra xs with
      | Some (z :: zs) => Some (Ira_Int (fold_left Z.min zs z))
      | Some [] => None
      | None =>
          match all_real_ra xs with
          | Some (r :: rs) => Some (Ira_Real (fold_left Rmin rs r))
          | Some [] => None
          | None => None
          end
      end

  | AggMax =>
      match all_int_ra xs with
      | Some (z :: zs) => Some (Ira_Int (fold_left Z.max zs z))
      | Some [] => None
      | None =>
          match all_real_ra xs with
          | Some (r :: rs) => Some (Ira_Real (fold_left Rmax rs r))
          | Some [] => None
          | None => None
          end
      end

  | AggSum =>
      match all_int_ra xs with
      | Some (z :: zs) => Some (Ira_Int (fold_left Z.add zs z))
      | Some [] => None
      | None =>
          match all_real_ra xs with
          | Some (r :: rs) => Some (Ira_Real (fold_left Rplus rs r))
          | Some [] => None
          | None => None
          end
      end
  end.






Fixpoint collect_col
  (grp : list RowData)
  (col : ColName)
  : list I_ra :=
  match grp with
  | [] => []
  | r :: rs =>
      match lookup_row_col col r with
      | Some v => v :: collect_col rs col
      | None   => collect_col rs col
      end
  end.


(* 
  在一个分组 grp 中，计算聚合后得到的列 c 的值。
  如果 c 不是一个聚合产生的列，返回 None；
  如果是，就按照聚合定义真正算出它的值。
*)
Definition eval_agg
  (grp  : list RowData)
  (c    : ColName)
  (aggs : list (ColName * aggop * ColName))
  : option I_ra :=
  match find
          (fun '(newc, _, _) => String.eqb newc c)
          aggs
  with
  | None =>
      (* c is not an aggregated column *)
      None
  | Some (_, op, srcCol) =>
      (* apply aggregation operator to source column values *)
      aggop_ra_sem op (collect_col grp srcCol)
  end.











(* 查找分组键值 *)
Fixpoint group_key (gcols : list ColName) (r : RowData)
  : option (list I_ra) :=
  match gcols with
  | [] => Some []
  | c :: cs =>
      match lookup_row_col c r, group_key cs r with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.





(* 比较 list I_ra 的相等：逐项 Ira_eqb *)
Fixpoint list_ira_eqb (xs ys : list I_ra) : bool :=
  match xs, ys with
  | [], [] => true
  | x::xs', y::ys' => andb (Ira_eqb x y) (list_ira_eqb xs' ys')
  | _, _ => false
  end.

(* 两行在 gcols 上的 key 是否相同（若某列缺失则视为不相同） *)
Definition same_keyb (gcols : list ColName) (r1 r2 : RowData) : bool :=
  match group_key gcols r1, group_key gcols r2 with
  | Some k1, Some k2 => list_ira_eqb k1 k2
  | _, _ => false
  end.

(* 把一行 r 插入到已有 groups 中：如果找到同 key 的组就加入，否则新开一组 *)
Fixpoint insert_group_rows
  (gcols : list ColName)
  (r : RowData)
  (groups : list (list RowData))
  : list (list RowData) :=
  match groups with
  | [] => [[r]]
  | grp :: rest =>
      match grp with
      | [] =>
          (* 空组不应出现，但为了总函数我们跳过它 *)
          grp :: insert_group_rows gcols r rest
      | r0 :: _ =>
          if same_keyb gcols r r0
          then (r :: grp) :: rest
          else grp :: insert_group_rows gcols r rest
      end
  end.

(* 主分组函数 *)
Fixpoint group_by_rows
  (gcols : list ColName)
  (rows : list RowData)
  : list (list RowData) :=
  match rows with
  | [] => []
  | r :: rs => insert_group_rows gcols r (group_by_rows gcols rs)
  end.








(* 从组里取 group-by 列的值：取第一行作为代表 *)
Definition take_group_cols
  (gcols : list ColName)
  (grp : list RowData)
  : option (list (ColName * I_ra)) :=
  match grp with
  | [] => None
  | r0 :: _ =>
      let fix aux (cs : list ColName) : option (list (ColName * I_ra)) :=
          match cs with
          | [] => Some []
          | c :: cs' =>
              match lookup_row_col c r0, aux cs' with
              | Some v, Some rest => Some ((c, v) :: rest)
              | _, _ => None
              end
          end
      in aux gcols
  end.

(* 计算一个组的所有聚合列 *)
Fixpoint eval_aggs_cols
  (grp  : list RowData)
  (aggs : list (ColName * aggop * ColName))
  : option (list (ColName * I_ra)) :=
  match aggs with
  | [] => Some []
  | (newc, op, src) :: tl =>
      match aggop_ra_sem op (collect_col grp src),
            eval_aggs_cols grp tl with
      | Some v, Some rest => Some ((newc, v) :: rest)
      | _, _ => None
      end
  end.


(* 构造单个组的输出行：key列 ++ agg列 *)
Definition build_group_row
  (gcols : list ColName)
  (aggs  : list (ColName * aggop * ColName))
  (grp   : list RowData)
  : option RowData :=
  match take_group_cols gcols grp, eval_aggs_cols grp aggs with
  | Some keyvs, Some aggvs => Some (List.app keyvs aggvs)
  | _, _ => None
  end.




(* 对所有组构造输出行：若任一组失败 => None *)
Fixpoint build_group_rows
  (gcols : list ColName)
  (aggs  : list (ColName * aggop * ColName))
  (groups : list (list RowData))
  : option (list RowData) :=
  match groups with
  | [] => Some []
  | grp :: tl =>
      match build_group_row gcols aggs grp,
            build_group_rows gcols aggs tl with
      | Some r, Some rs => Some (r :: rs)
      | _, _ => None
      end
  end.





Definition scalar_extract (cn : ColName) (rows : list RowData) : option I_ra :=
  match rows with
  | [r] => lookup_row cn r
  | _   => None
  end.





Definition val_col : ColName := "_val".

(*************************************************************)
(*      Relational Algebra Big-step Semantics (Relation)     *)
(*************************************************************)




(* 互递归：evalRelR <-> evalRexR
   因为 RSubquery 里需要 evalRelR。 *)
Inductive evalRelR ( SC: Schema) : DBInstance SC -> rel -> list RowData -> Prop :=

  | ER_Empty :
      forall (DB : DBInstance SC),
        evalRelR SC DB RAEmpty []

  | ER_BagLiteral :
      forall (DB : DBInstance SC) (t : T_ra) (vl : list I_ra),
        evalRelR SC DB (RABagLiteral t vl)
          (map (fun v => [(val_col, v)]) vl)
          
  | ER_Table :
      forall (DB : DBInstance SC) (t : TableName) (rows : list RowData),
        (db_data SC DB) t = Some rows ->
        evalRelR SC DB (RATable t) rows

  (* 选择：用生成关系 select_rowsR *)
  | ER_Select :
      forall (DB : DBInstance SC) (cond : rex) (q : rel)
            (rows rows' : list RowData),
        evalRelR SC DB q rows ->
        select_rowsR SC DB cond rows rows' ->
        evalRelR SC DB (RASelect cond q) rows'

  (* 投影：用生成关系 project_rowsR *)
  | ER_Project :
      forall (DB : DBInstance SC) (ps : list (ColName * rex)) (q : rel)
            (rows rows' : list RowData),
        evalRelR SC DB q rows ->
        Forall2 (project_rowR SC DB ps) rows rows' ->
        evalRelR SC DB (RAProject ps q) rows'

  (* 笛卡尔积：用生成关系 cartesian_rowsR *)
  | ER_Cartesian :
      forall (DB : DBInstance SC) (q1 q2 : rel)
            (rows1 rows2 rows' : list RowData),
        evalRelR SC DB q1 rows1 ->
        evalRelR SC DB q2 rows2 ->
        cartesian_rowsR SC DB rows1 rows2 rows' ->
        evalRelR SC DB (RACartesian q1 q2) rows'

  (* join：最干净的组织方式：join = select cond (cartesian q1 q2) *)
  | ER_Join :
      forall (DB : DBInstance SC) (cond : rex) (q1 q2 : rel)
            (rows1 rows2 rowsCart rows' : list RowData),
        evalRelR SC DB q1 rows1 ->
        evalRelR SC DB q2 rows2 ->
        cartesian_rowsR SC DB rows1 rows2 rowsCart ->
        select_rowsR SC DB cond rowsCart rows' ->
        evalRelR SC DB (RAJoin cond q1 q2) rows'

  | ER_Union :
      forall (DB : DBInstance SC) (q1 q2 : rel)
            (rows1 rows2 : list RowData),
        evalRelR SC DB q1 rows1 ->
        evalRelR SC DB q2 rows2 ->
        evalRelR SC DB (RAUnion q1 q2) (rows1 ++ rows2)

  | ER_Diff :
      forall (DB : DBInstance SC) (q1 q2 : rel)
            (rows1 rows2 rows' : list RowData),
        evalRelR SC DB q1 rows1 ->
        evalRelR SC DB q2 rows2 ->
        bag_diff_rows rows1 rows2 = rows' ->
        evalRelR SC DB (RADiff q1 q2) rows'

  | ER_Distinct :
      forall (DB : DBInstance SC) (q : rel)
            (rows rows' : list RowData),
        evalRelR SC DB q rows ->
        remove_dup_rows rows = rows' ->
        evalRelR SC DB (RADistinct q) rows'

  | ER_Aggregate :
      forall (DB : DBInstance SC)
            (gcols : list ColName)
            (aggs  : list (ColName * aggop * ColName))
            (q : rel) (rows : list RowData)
            (groups : list (list RowData)) (rows' : list RowData),
        evalRelR SC DB q rows ->
        groups = group_by_rows gcols rows ->
        build_group_rows gcols aggs groups = Some rows' ->
        evalRelR SC DB (RAAggregate gcols aggs q) rows'



  with evalRexR ( SC: Schema) : DBInstance SC -> RowData -> rex -> I_ra -> Prop :=
    | ER_Col :
        forall (DB : DBInstance SC) row cn v,
          lookup_row cn row = Some v ->
          evalRexR SC DB row (RCol cn) v

    | ER_Val :
        forall (DB : DBInstance SC) row v,
          evalRexR SC DB row (RLit v) v

    | ER_Unop :
        forall (DB : DBInstance SC) row op e1 v1 v,
          evalRexR SC DB row e1 v1 ->
          unop_sem_ra op v1 = Some v ->
          evalRexR SC DB row (RUnop op e1) v

    | ER_Binop :
        forall (DB : DBInstance SC) row op e1 e2 v1 v2 v,
          evalRexR SC DB row e1 v1 ->
          evalRexR SC DB row e2 v2 ->
          binop_sem_ra op v1 v2 = Some v ->
          evalRexR SC DB row (RBinop op e1 e2) v

    | ER_Subquery :
        forall (DB : DBInstance SC) row (q : rel) (cn : ColName) rows v,
          evalRelR SC DB q rows ->
          scalar_extract cn rows = Some v ->
          evalRexR SC DB row (RSubquery q cn) v



    (* --------------------------------------------------------- *)
    (* 2) 行->行：投影一行 / 合并两行                             *)
    (* --------------------------------------------------------- *)

    with project_rowR ( SC: Schema) : DBInstance SC -> list (ColName * rex) -> RowData -> RowData -> Prop :=
      | ProjectRowR :
          forall (DB : DBInstance SC) (ps : list (ColName * rex)) (r : RowData) (vs : list I_ra),
            (* 建议加 NoDup，避免同名列导致 lookup_row 歧义 *)
            NoDup (map fst ps) ->
            Forall2 (fun p v => evalRexR SC DB r (snd p) v) ps vs ->
            project_rowR SC DB ps r (combine (map fst ps) vs)

    with cartesian_rowR ( SC: Schema) : DBInstance SC -> RowData -> RowData -> RowData -> Prop :=
      | CartesianRow_intro :
          forall (DB : DBInstance SC) r1 r2,
            NoDup (row_cols r1) ->
            NoDup (row_cols r2) ->
            disjoint_cols r1 r2 ->
            cartesian_rowR SC DB r1 r2 (row_merge r1 r2)

    (* --------------------------------------------------------- *)
    (* 3) 列表级生成关系：select/project/cartesian                 *)
    (* --------------------------------------------------------- *)

    with select_rowsR ( SC: Schema) : DBInstance SC -> rex -> list RowData -> list RowData -> Prop :=
      | SR_nil :
          forall (DB : DBInstance SC) cond,
            select_rowsR SC DB cond [] []
      | SR_keep :
          forall (DB : DBInstance SC) cond r rs rs',
            evalRexR SC DB r cond (Ira_Bool true) ->
            select_rowsR SC DB cond rs rs' ->
            select_rowsR SC DB cond (r :: rs) (r :: rs')
      | SR_drop_false :
          forall (DB : DBInstance SC) cond r rs rs',
            evalRexR SC DB r cond (Ira_Bool false) ->
            select_rowsR SC DB cond rs rs' ->
            select_rowsR SC DB cond (r :: rs) rs'


    with cartesian_rowsR ( SC: Schema) : DBInstance SC -> list RowData -> list RowData -> list RowData -> Prop :=
      | CR_nil :
          forall (DB : DBInstance SC) rows2,
            cartesian_rowsR SC DB [] rows2 []
      | CR_cons :
          forall (DB : DBInstance SC) r1 rows1 rows2 out1 outRest,
            (* out1 是 r1 与 rows2 的所有合并结果（以 list 形式生成） *)
            cartesian_rows_oneR SC DB r1 rows2 out1 ->
            cartesian_rowsR SC DB rows1 rows2 outRest ->
            cartesian_rowsR SC DB (r1 :: rows1) rows2 (out1 ++ outRest)

    with cartesian_rows_oneR ( SC: Schema) : DBInstance SC -> RowData -> list RowData -> list RowData -> Prop :=
      | CRO_nil :
          forall (DB : DBInstance SC) r1,
            cartesian_rows_oneR SC DB r1 [] []
      | CRO_cons :
          forall (DB : DBInstance SC) r1 r2 rs2 r' outRest,
            cartesian_rowR SC DB r1 r2 r' ->
            cartesian_rows_oneR SC DB r1 rs2 outRest ->
            cartesian_rows_oneR SC DB r1 (r2 :: rs2) (r' :: outRest)
    .

















(* 函数方式定义的RA语义 *)

Fixpoint select_rowsF
  (evalRex : RowData -> rex -> option I_ra)
  (cond : rex) (rows : list RowData)
  : option (list RowData) :=
  match rows with
  | [] => Some []
  | r :: rs =>
      match evalRex r cond, select_rowsF evalRex cond rs with
      | Some (Ira_Bool true),  Some out => Some (r :: out)
      | Some (Ira_Bool false), Some out => Some out
      | _, _ => None
      end
  end.

Fixpoint eval_proj_valsF
  (evalRex : RowData -> rex -> option I_ra)
  (r : RowData) (ps : list (ColName * rex))
  : option (list I_ra) :=
  match ps with
  | [] => Some []
  | (_, e) :: tl =>
      match evalRex r e, eval_proj_valsF evalRex r tl with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

Definition project_rowF
  (evalRex : RowData -> rex -> option I_ra)
  (ps : list (ColName * rex)) (r : RowData)
  : option RowData :=
  match eval_proj_valsF evalRex r ps with
  | Some vs => Some (combine (map fst ps) vs)
  | None => None
  end.

Fixpoint project_rowsF
  (evalRex : RowData -> rex -> option I_ra)
  (ps : list (ColName * rex)) (rows : list RowData)
  : option (list RowData) :=
  match rows with
  | [] => Some []
  | r :: rs =>
      match project_rowF evalRex ps r, project_rowsF evalRex ps rs with
      | Some r', Some out => Some (r' :: out)
      | _, _ => None
      end
  end.

Fixpoint cartesian_rowsF (rows1 rows2 : list RowData) : list RowData :=
  match rows1 with
  | [] => []
  | r1 :: tl =>
      (map (fun r2 => row_merge r1 r2) rows2) ++ cartesian_rowsF tl rows2
  end.




Fixpoint evalRelF
  (SC : Schema) (DB : DBInstance SC) (q : rel)
  : option (list RowData) :=
  match q with
  | RAEmpty =>
      Some []

  | RABagLiteral t vl =>
      Some (map (fun v => [(val_col, v)]) vl)

  | RATable t =>
      db_data SC DB t

  | RASelect cond q1 =>
      match evalRelF SC DB q1 with
      | Some rows =>
          select_rowsF (fun r e => evalRexF SC DB r e) cond rows
      | None => None
      end

  | RAProject ps q1 =>
      match evalRelF SC DB q1 with
      | Some rows =>
          project_rowsF (fun r e => evalRexF SC DB r e) ps rows
      | None => None
      end

  | RACartesian q1 q2 =>
      match evalRelF SC DB q1, evalRelF SC DB q2 with
      | Some rows1, Some rows2 => Some (cartesian_rowsF rows1 rows2)
      | _, _ => None
      end

  | RAJoin cond q1 q2 =>
      match evalRelF SC DB q1, evalRelF SC DB q2 with
      | Some rows1, Some rows2 =>
          select_rowsF (fun r e => evalRexF SC DB r e) cond
            (cartesian_rowsF rows1 rows2)
      | _, _ => None
      end

  | RAUnion q1 q2 =>
      match evalRelF SC DB q1, evalRelF SC DB q2 with
      | Some rows1, Some rows2 => Some (List.app rows1 rows2)
      | _, _ => None
      end

  | RADiff q1 q2 =>
      match evalRelF SC DB q1, evalRelF SC DB q2 with
      | Some rows1, Some rows2 => Some (bag_diff_rows rows1 rows2)
      | _, _ => None
      end

  | RADistinct q1 =>
      match evalRelF SC DB q1 with
      | Some rows => Some (remove_dup_rows rows)
      | None => None
      end

  | RAAggregate gcols aggs q1 =>
      match evalRelF SC DB q1 with
      | Some rows =>
          let groups := group_by_rows gcols rows in
          build_group_rows gcols aggs groups
      | None => None
      end
  end

with evalRexF
  (SC : Schema) (DB : DBInstance SC) (row : RowData) (e : rex)
  : option I_ra :=
  match e with
  | RCol cn =>
      lookup_row cn row

  | RLit v =>
      Some v

  | RUnop op e1 =>
      match evalRexF SC DB row e1 with
      | Some v1 => unop_sem_ra op v1
      | None => None
      end

  | RBinop op e1 e2 =>
      match evalRexF SC DB row e1, evalRexF SC DB row e2 with
      | Some v1, Some v2 => binop_sem_ra op v1 v2
      | _, _ => None
      end

  | RSubquery q cn =>
      match evalRelF SC DB q with
      | Some rows => scalar_extract cn rows
      | None => None
      end
  end.





Lemma evalRelF_det :
  forall SC (DB : DBInstance SC) q rows1 rows2,
    evalRelF SC DB q = Some rows1 ->
    evalRelF SC DB q = Some rows2 ->
    rows1 = rows2.
Proof. intros; congruence. Qed.



