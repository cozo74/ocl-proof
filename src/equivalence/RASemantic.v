(*************************************************************)
(*                                                           *)
(*        Relational Algebra Semantics (Big-step)             *)
(*                                                           *)
(*  Design principles:                                       *)
(*  - RexNode: row-level, pure, no DB access                 *)
(*  - ra_rel  : relation-level, evaluated over DBInstance     *)
(*                                                           *)
(*************************************************************)

From Stdlib Require Import String List ZArith Reals Bool.
From Stdlib Require Import Program.Wf Arith Lia.
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
  | Ira_Bool a, Ira_Bool b => Some (Bool.eqb a b)
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
  : option (list I_ra) :=
  match grp with
  | [] => Some []
  | r :: rs =>
      match lookup_row_col col r, collect_col rs col with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
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
  match find (fun '(newc, _, _) => String.eqb newc c) aggs with
  | None => None
  | Some (_, op, srcCol) =>
      match collect_col grp srcCol with
      | Some xs => aggop_ra_sem op xs
      | None => None
      end
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
      match collect_col grp src, eval_aggs_cols grp tl with
      | Some xs, Some rest =>
          match aggop_ra_sem op xs with
          | Some v => Some ((newc, v) :: rest)
          | None => None
          end
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



(* 
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
        gcols <> [] ->
        aggs  <> [] ->
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
        forall (DB : DBInstance SC) row
              (agg : ColName * aggop) (q : rel)
              rows xs v,
          evalRelR SC DB q rows ->
          collect_col rows (fst agg) = Some xs ->
          aggop_ra_sem (snd agg) xs = Some v ->
          evalRexR SC DB row (RSubquery agg q) v



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
 *)
















(* 函数方式定义的RA语义 *)


Fixpoint nodup_stringb (xs : list string) : bool :=
  match xs with
  | [] => true
  | x :: tl =>
      negb (existsb (String.eqb x) tl)
      && nodup_stringb tl
  end.






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
  if nodup_stringb (map fst ps)
  then
    match eval_proj_valsF evalRex r ps with
    | Some vs => Some (combine (map fst ps) vs)
    | None => None
    end
  else None.

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





Fixpoint in_stringb (x : string) (xs : list string) : bool :=
  match xs with
  | [] => false
  | y :: ys => if String.eqb x y then true else in_stringb x ys
  end.

Definition disjoint_cols_b (r1 r2 : RowData) : bool :=
  negb (existsb (fun c => andb (in_stringb c (row_cols r1))
                               (in_stringb c (row_cols r2)))
                (row_cols r1)).

  


Definition cartesian_rowF (r1 r2 : RowData) : option RowData :=
  if nodup_stringb (row_cols r1)
  then if nodup_stringb (row_cols r2)
       then if disjoint_cols_b r1 r2
            then Some (row_merge r1 r2)
            else None
       else None
  else None.




Fixpoint option_map_list {A B : Type} (f : A -> option B) (xs : list A)
  : option (list B) :=
  match xs with
  | [] => Some []
  | x :: tl =>
      match f x, option_map_list f tl with
      | Some y, Some ys => Some (y :: ys)
      | _, _ => None
      end
  end.

Definition option_app {A : Type} (ox oy : option (list A)) : option (list A) :=
  match ox, oy with
  | Some xs, Some ys => Some (List.app xs ys)
  | _, _ => None
  end.


Definition cartesian_rows_oneF (r1 : RowData) (rows2 : list RowData)
  : option (list RowData) :=
  option_map_list (fun r2 => cartesian_rowF r1 r2) rows2.

Fixpoint cartesian_rowsF (rows1 rows2 : list RowData)
  : option (list RowData) :=
  match rows1 with
  | [] => Some []
  | r1 :: tl =>
      option_app (cartesian_rows_oneF r1 rows2)
                 (cartesian_rowsF tl rows2)
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
      | Some rows1, Some rows2 => cartesian_rowsF rows1 rows2
      | _, _ => None
      end

  | RAJoin cond q1 q2 =>
      match evalRelF SC DB q1, evalRelF SC DB q2 with
      | Some rows1, Some rows2 =>
          match cartesian_rowsF rows1 rows2 with
          | Some rowsCart => select_rowsF (evalRexF SC DB) cond rowsCart
          | None => None
          end
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
      match gcols with
      | [] => None
      | _ :: _ =>
        match aggs with
        | [] => None
        | _ :: _ =>
          match evalRelF SC DB q1 with
          | Some rows =>
              let groups := group_by_rows gcols rows in
              build_group_rows gcols aggs groups
          | None => None
          end
        end
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

    | RSubquery a q =>
        match a with
        | (cn, op) =>
            match evalRelF SC DB q with
            | Some rows =>
                match collect_col rows cn with
                | Some xs => aggop_ra_sem op xs
                | None => None
                end
            | None => None
            end
        end
    end.





(* Lemma evalRelF_det :
  forall SC (DB : DBInstance SC) q rows1 rows2,
    evalRelF SC DB q = Some rows1 ->
    evalRelF SC DB q = Some rows2 ->
    rows1 = rows2.
Proof. intros; congruence. Qed. *)






(* Lemma existsb_string_eqb_of_in :
  forall (x : string) (xs : list string),
    In x xs -> existsb (String.eqb x) xs = true.
Proof.
  intros x xs Hin.
  induction xs as [|y ys IH]; cbn in *.
  - contradiction.
  - destruct Hin as [<- | Hin].
    + (* x = y *)
      rewrite String.eqb_refl. reflexivity.
    + (* x in ys *)
      destruct (String.eqb x y) eqn:Heq.
      * reflexivity.
      * apply IH. exact Hin.
Qed. *)




(* Lemma nodup_stringb_sound :
  forall xs, nodup_stringb xs = true -> NoDup xs.
Proof.
  intros xs; induction xs as [|x tl IH]; cbn.
  - intros. constructor.
  - intro H.
    apply andb_true_iff in H as [Hnotin Hnodup].
    apply negb_true_iff in Hnotin.
    constructor.
    + (* ~ In x tl *)
      intro Hin.
      (* 用 existsb_exists 推出 existsb = true，矛盾 *)
      assert (Hex : existsb (String.eqb x) tl = true).
      { apply existsb_string_eqb_of_in. exact Hin. }
      rewrite Hex in Hnotin. discriminate.
    + (* NoDup tl *)
      apply IH. exact Hnodup.
Qed. *)






(* 

Lemma select_rowsF_sound_gen
  (SC : Schema) (DB : DBInstance SC)
  (evalRex : RowData -> rex -> option I_ra)
  (cond : rex) (rows out : list RowData) :
  (forall r e v, evalRex r e = Some v -> evalRexR SC DB r e v) ->
  select_rowsF evalRex cond rows = Some out ->
  select_rowsR SC DB cond rows out.
Proof.
  intros Hrex.
  revert out.
  induction rows as [|r rs IH]; intros out Hsel.
  - simpl in Hsel. inversion Hsel; subst. constructor.
  - simpl in Hsel.
    destruct (evalRex r cond) as [v|] eqn:Hv; try discriminate.
    destruct (select_rowsF evalRex cond rs) as [out'|] eqn:Hrec; try discriminate.
    destruct v; try discriminate.
    destruct b. inversion Hsel; subst; econstructor; eauto.
    + inversion Hsel; subst.
      econstructor.
      * eapply (Hrex r cond (Ira_Bool false)); eauto.
      * eapply IH; eauto.
    + inversion Hsel; subst.
      econstructor; destruct v; cbn in Hsel; try discriminate Hsel;
      destruct b; cbn in Hsel; discriminate Hsel.
Qed. *)




(* ------------------------------------------------------------ *)
(* 1) eval_proj_valsF 的 soundness（泛化 evalRex）              *)
(* ------------------------------------------------------------ *)

(* Lemma eval_proj_valsF_sound_gen
  (SC : Schema) (DB : DBInstance SC)
  (evalRex : RowData -> rex -> option I_ra)
  (r : RowData) (ps : list (ColName * rex)) (vs : list I_ra) :
  (forall r e v, evalRex r e = Some v -> evalRexR SC DB r e v) ->
  eval_proj_valsF evalRex r ps = Some vs ->
  Forall2 (fun p v => evalRexR SC DB r (snd p) v) ps vs.
Proof.
  intros Hrex.
  revert vs.
  induction ps as [|[cn e] tl IH]; intros vs Heq.
  - simpl in Heq. inversion Heq; subst. constructor.
  - simpl in Heq.
    destruct (evalRex r e) as [v|] eqn:Hv; try discriminate.
    destruct (eval_proj_valsF evalRex r tl) as [vs'|] eqn:Htl; try discriminate.
    inversion Heq; subst.
    constructor.
    + (* head *)
      eapply (Hrex r e v); eauto.
    + (* tail *)
      eapply IH; eauto.
Qed. *)



(* ------------------------------------------------------------ *)
(* 2) project_rowF 的 soundness（泛化 evalRex）                 *)
(* ------------------------------------------------------------ *)



(* Lemma project_rowF_sound_gen
  (SC : Schema) (DB : DBInstance SC)
  (evalRex : RowData -> rex -> option I_ra)
  (ps : list (ColName * rex)) (r r' : RowData) :
  (forall r0 e v, evalRex r0 e = Some v -> evalRexR SC DB r0 e v) ->
  project_rowF evalRex ps r = Some r' ->
  project_rowR SC DB ps r r'.
Proof.
  intros Hrex Hf.
  unfold project_rowF in Hf.
  destruct (nodup_stringb (map fst ps)) eqn:Hnd; try discriminate.
  destruct (eval_proj_valsF evalRex r ps) eqn:Hv; try discriminate.
  inversion Hf; subst r'. clear Hf.

  pose proof (nodup_stringb_sound (map fst ps) Hnd) as HNoDup.
  pose proof (eval_proj_valsF_sound_gen SC DB evalRex r ps l Hrex Hv) as HForall2.

  econstructor; eauto.
Qed. *)



(* ------------------------------------------------------------ *)
(* 3) project_rowsF 的 soundness（泛化 evalRex）                *)
(* ------------------------------------------------------------ *)

(* Lemma project_rowsF_sound_gen
  (SC : Schema) (DB : DBInstance SC)
  (evalRex : RowData -> rex -> option I_ra)
  (ps : list (ColName * rex))
  (rows out : list RowData) :
  (forall r e v, evalRex r e = Some v -> evalRexR SC DB r e v) ->
  NoDup (map fst ps) ->
  project_rowsF evalRex ps rows = Some out ->
  Forall2 (project_rowR SC DB ps) rows out.
Proof.
  intros Hrex Hnodup.
  revert out.
  induction rows as [|r rs IH]; intros out Hrows.
  - simpl in Hrows. inversion Hrows; subst. constructor.
  - simpl in Hrows.
    destruct (project_rowF evalRex ps r) as [r1|] eqn:Hr; try discriminate.
    destruct (project_rowsF evalRex ps rs) as [out'|] eqn:Hrs; try discriminate.
    inversion Hrows; subst.
    constructor.
    + eapply project_rowF_sound_gen; eauto.
    + eapply IH; eauto.
Qed. *)


(* Lemma project_rowsF_sound_Forall2_gen
  (SC : Schema) (DB : DBInstance SC)
  (evalRex : RowData -> rex -> option I_ra)
  (ps : list (ColName * rex))
  (rows rows' : list RowData) :
  (forall r e v, evalRex r e = Some v -> evalRexR SC DB r e v) ->
  project_rowsF evalRex ps rows = Some rows' ->
  Forall2 (project_rowR SC DB ps) rows rows'.
Proof.
  intros Hrex.
  revert rows'.
  induction rows as [|r rs IH]; intros rows' Hproj.
  - simpl in Hproj. inversion Hproj; subst. constructor.
  - simpl in Hproj.
  (* goal: Forall2 (project_rowR SC DB ps) (r :: rs) rows' *)

  destruct (project_rowF evalRex ps r) as [r'|] eqn:Hr; try discriminate.
  destruct (project_rowsF evalRex ps rs) as [out|] eqn:Hrs; try discriminate.
  inversion Hproj; subst.

  constructor.
  + (* 需要：project_rowR SC DB ps r r' *)
    (* 这里用你应该有的单行 soundness 引理 *)
    eapply project_rowF_sound_gen; eauto.
  + (* 需要：Forall2 ... rs out *)
    eapply IH; eauto.
Qed. *)



(* ---------- 1) in_stringb 与正确性 ---------- *)


(* Lemma in_stringb_true_iff :
  forall x xs, in_stringb x xs = true <-> In x xs.
Proof.
  intros x xs; induction xs as [|y ys IH]; cbn.
  - split; intro H; try discriminate; contradiction.
  - destruct (String.eqb x y) eqn:Heq.
    + apply String.eqb_eq in Heq; subst.
      split; intro; [left; reflexivity| reflexivity].
    + split.
      * intro H. right. apply IH. exact H.
      * intro Hin. destruct Hin as [Hin|Hin].
        { subst. rewrite String.eqb_refl in Heq. discriminate. }
        apply IH. exact Hin.
Qed.


Lemma in_stringb_false_iff :
  forall x xs, in_stringb x xs = false <-> ~ In x xs.
Proof.
  intros x xs.
  rewrite <- in_stringb_true_iff.
  destruct (in_stringb x xs); cbn; split; intro H; try discriminate; auto. 
  contradiction.
Qed. *)




(* ---------- 2) NoDup 的 bool 判定 + sound ---------- *)




(* Lemma disjoint_cols_b_sound :
  forall r1 r2,
    disjoint_cols_b r1 r2 = true ->
    disjoint_cols r1 r2.
Proof.
  intros r1 r2 Hb c.
  unfold disjoint_cols_b in Hb.
  apply negb_true_iff in Hb.
  unfold disjoint_cols.
  intro Hboth.
  destruct Hboth as [HIn1 HIn2].
  (* 由 HIn1 得到 existsb 为 true，矛盾 *)
  assert (Hex : existsb
    (fun c0 : string =>
       andb (in_stringb c0 (row_cols r1))
            (in_stringb c0 (row_cols r2)))
    (row_cols r1) = true).
  {
    apply existsb_exists.
    exists c.
    split; [exact HIn1|].
    (* 证明 andb ... = true *)
    apply andb_true_iff.
    split.
    - apply (proj2 (in_stringb_true_iff c (row_cols r1))). exact HIn1.
    - apply (proj2 (in_stringb_true_iff c (row_cols r2))). exact HIn2.
  }
  rewrite Hex in Hb. discriminate.
Qed. *)



(* Lemma cartesian_rowF_sound :
  forall SC (DB : DBInstance SC) r1 r2 r',
    cartesian_rowF r1 r2 = Some r' ->
    cartesian_rowR SC DB r1 r2 r'.
Proof.
  intros SC DB r1 r2 r' H.
  unfold cartesian_rowF in H.
  destruct (nodup_stringb (row_cols r1)) eqn:Hn1; try discriminate.
  destruct (nodup_stringb (row_cols r2)) eqn:Hn2; try discriminate.
  destruct (disjoint_cols_b r1 r2) eqn:Hd; try discriminate.
  inversion H; subst r'. clear H.

  (* 从 bool -> Prop *)
  pose proof (nodup_stringb_sound _ Hn1) as Hnd1.
  pose proof (nodup_stringb_sound _ Hn2) as Hnd2.
  pose proof (disjoint_cols_b_sound r1 r2 Hd) as Hdisj.

  (* 用 inductive 构造子 *)
  constructor; auto.
Qed. *)





(* Lemma cartesian_rows_oneF_sound :
  forall SC (DB : DBInstance SC) r1 rows2 out,
    cartesian_rows_oneF r1 rows2 = Some out ->
    cartesian_rows_oneR SC DB r1 rows2 out.
Proof.
  intros SC DB r1 rows2.
  induction rows2 as [|r2 rs2 IH]; intros out H.
  - cbn in H. inversion H; subst. constructor.
  - cbn in H.
    unfold cartesian_rows_oneF in H; cbn in H.
    (* option_map_list 展开 *)
    cbn in H.
    destruct (cartesian_rowF r1 r2) eqn:Hrow; try discriminate.
    destruct (option_map_list (fun r => cartesian_rowF r1 r) rs2) eqn:Hrec; try discriminate.
    inversion H; subst out. clear H.
    econstructor.
    + eapply cartesian_rowF_sound; eauto.
    + (* 递归 *)
      (* 注意：IH 需要输入 out0 *)
      eapply IH; eauto.
Qed. *)

(* Lemma cartesian_rowsF_sound :
  forall SC (DB : DBInstance SC) rows1 rows2 out,
    cartesian_rowsF rows1 rows2 = Some out ->
    cartesian_rowsR SC DB rows1 rows2 out.
Proof.
  intros SC DB rows1.
  induction rows1 as [|r1 tl IH]; intros rows2 out H.
  - cbn in H. inversion H; subst. constructor.
  - cbn in H.
    (* option_app 分析 *)
    unfold option_app in H.
    destruct (cartesian_rows_oneF r1 rows2) eqn:Hone; try discriminate.
    destruct (cartesian_rowsF tl rows2) eqn:Hrest; try discriminate.
    inversion H; subst out. clear H.
    econstructor.
    + eapply cartesian_rows_oneF_sound; eauto.
    + eapply IH; eauto.
Qed. *)











(* 

Lemma evalRelF_sound :
  forall SC (DB:DBInstance SC) q rows,
    evalRelF SC DB q = Some rows ->
    evalRelR SC DB q rows
with evalRexF_sound :
  forall SC (DB:DBInstance SC) row e v,
    evalRexF SC DB row e = Some v ->
    evalRexR SC DB row e v.
Proof.
  (* ======================= evalRelF_sound ======================= *)
    - intros SC DB q rows Heq.
    revert rows Heq.
    induction q; intros rows Heq; cbn in Heq.
    + (* RAEmpty *)
      inversion Heq; subst. constructor.
    + (* RABagLiteral *)
      inversion Heq; subst. constructor.
    + (* RATable *)
      (* evalRelF = db_data SC DB t *)
      econstructor. exact Heq.

    + (* RASelect cond q *)
      destruct (evalRelF SC DB q) eqn:Hq; try discriminate.
      assert (HqR : evalRelR SC DB q l).
      { apply IHq. reflexivity. }
      assert (HselR : select_rowsR SC DB r l rows).
      {
        eapply (select_rowsF_sound_gen
                  SC DB
                  (fun rw e => evalRexF SC DB rw e)
                  r l rows).
        - intros rw e v Hv. eapply evalRexF_sound; eauto.
        - exact Heq.
      }
      eapply ER_Select; eauto.

    + (* RAProject ps q *)
      destruct (evalRelF SC DB q) eqn:Hq; try discriminate.
      assert (HqR : evalRelR SC DB q l0).
      { apply IHq. reflexivity. }
      assert (Hproj : Forall2 (project_rowR SC DB l) l0 rows).
      {
        eapply (project_rowsF_sound_Forall2_gen
                  SC DB
                  (fun rw e => evalRexF SC DB rw e)
                  l l0 rows).
        - intros rw e v Hv. eapply evalRexF_sound; eauto.
        - exact Heq.
      }
      eapply ER_Project; eauto.

    + (* RACartesian q1 q2 *)
      destruct (evalRelF SC DB q1) eqn:H1; try discriminate.
      destruct (evalRelF SC DB q2) eqn:H2; try discriminate.
      assert (Hq1R : evalRelR SC DB q1 l).
      { apply IHq1. reflexivity. }
      assert (Hq2R : evalRelR SC DB q2 l0).
      { apply IHq2. reflexivity. }
      assert (Hcart : cartesian_rowsR SC DB l l0 rows).
      { eapply cartesian_rowsF_sound; eauto. }
      (* 用构造子拼起来；避免隐式参数错位，用 @ 或 econstructor *)
      econstructor; eauto.

    + (* RAJoin cond q1 q2 *)
      destruct (evalRelF SC DB q1) eqn:H1; try discriminate.
      destruct (evalRelF SC DB q2) eqn:H2; try discriminate.
      destruct (cartesian_rowsF l l0) eqn:Hcart; try discriminate.
      assert (Hq1R : evalRelR SC DB q1 l).
      { apply IHq1. reflexivity. }
      assert (Hq2R : evalRelR SC DB q2 l0).
      { apply IHq2. reflexivity. }
      assert (HcartR : cartesian_rowsR SC DB l l0 l1).
      { eapply cartesian_rowsF_sound; eauto. }
      assert (HselR : select_rowsR SC DB r l1 rows).
      {
        eapply (select_rowsF_sound_gen
                  SC DB
                  (fun rw e => evalRexF SC DB rw e)
                  r l1 rows).
        - intros rw e v Hv. eapply evalRexF_sound; eauto.
        - exact Heq.
      }

      eapply ER_Join; eauto.

    + (* RAUnion q1 q2 *)
      destruct (evalRelF SC DB q1) eqn:H1; try discriminate.
      destruct (evalRelF SC DB q2) eqn:H2; try discriminate.
      inversion Heq; subst rows.
      eapply ER_Union; [eapply IHq1|eapply IHq2]; eauto.

    + (* RADiff q1 q2 *)
      destruct (evalRelF SC DB q1) eqn:H1; try discriminate.
      destruct (evalRelF SC DB q2) eqn:H2; try discriminate.
      inversion Heq; subst rows.
      eapply ER_Diff; [eapply IHq1|eapply IHq2|]; eauto.

    + (* RADistinct q *)
      destruct (evalRelF SC DB q) eqn:Hq; try discriminate.
      inversion Heq; subst rows.
      eapply ER_Distinct; [eapply IHq|]; eauto.

    + (* RAAggregate gcols aggs q *)
      (* RAAggregate gcols aggs q *)
      destruct l as [|c l']; cbn in Heq; try discriminate.
      destruct l0 as [|a l0']; cbn in Heq; try discriminate.
      destruct (evalRelF SC DB q) as [rows_q|] eqn:Hq; try discriminate.
      assert (HqR : evalRelR SC DB q rows_q).
      { apply (IHq rows_q). reflexivity. }

      set (groups := group_by_rows (c :: l') rows_q).

      eapply ER_Aggregate with (rows := rows_q) (groups := groups); eauto.
      -- discriminate.
      -- discriminate.





  (* ======================= evalRexF_sound ======================= *)
  - intros SC DB row e v Heq.
    revert v Heq.
    induction e; intros v Heq; cbn in Heq.
    + (* RCol *)
      econstructor. exact Heq.
    + (* RLit *)
      inversion Heq; subst. constructor.
    + (* RUnop *)
      destruct (evalRexF SC DB row e) eqn:He1; try discriminate.
      assert (HeR : evalRexR SC DB row e i).
      { apply IHe. reflexivity. }
      (* 然后用一元运算的关系语义构造子 *)
      eapply ER_Unop; eauto.

    + (* RBinop *)
      destruct (evalRexF SC DB row e1) eqn:H1; try discriminate.
      destruct (evalRexF SC DB row e2) eqn:H2; try discriminate.
      assert (He1R : evalRexR SC DB row e1 i).
      { apply IHe1. reflexivity. }
      assert (He2R : evalRexR SC DB row e2 i0).
      { apply IHe2. reflexivity. }
      eapply ER_Binop; eauto.
    + (* RSubquery *)
      cbn in Heq.
      destruct p as [cn op]. cbn in Heq.
      destruct (evalRelF SC DB r) as [rows|] eqn:Hr; try discriminate.
      destruct (collect_col rows cn) as [xs|] eqn:Hcol; try discriminate.

      (* 此时 Heq : aggop_ra_sem op xs = Some v *)
      (* 先把子查询 r 的关系语义拿到 *)
      pose proof (evalRelF_sound SC DB r rows Hr) as HrR.

      (* 用 ER_Subquery 拼起来 *)
      eapply ER_Subquery; eauto.


Qed. *)


