From Stdlib Require Import String ZArith Reals List.
Import ListNotations.
Open Scope string_scope.

From OCL.equivalence Require Import Models Utils.
From OCL.equivalence Require Import OCLSyntax OCLSemantic.
From OCL.equivalence Require Import RASyntax RASemantic.
From OCL.equivalence Require Import Translation. 

From Stdlib Require Import Permutation.
From Stdlib Require Import Program.Equality.






(* 语法糖：class.allInstances->select(self | not expr) *)
Definition inv_tm (C : class_name) (expr : tm) : tm :=
  CSelect (CAllInstances C) "self" (CUnop (U_Bool UNot) expr).



(**
  ocl_obj_bag_oids C xs
  从一个 OCL 对象 bag（list I_h）中提取属于类 C 的对象标识符列表。
  语义：
  - xs 必须是一个纯对象 bag
  - 且每个元素必须是 Ih_Object C o
  - 如果遇到：
      * 非对象值
      * 或对象但类名 ≠ C
    → 整个提取失败，返回 None

  成功时：
      Some [o1; o2; ...; on]

  这个函数是一个“类型安全投影”：
      Bag(Object C)  →  option (list oid)

  失败表示：bag 不是同构的 C 对象集合。
*)
Definition ocl_obj_bag_oids (C : class_name) (xs : list I_h) : option (list oid) :=
  let fix go (ys : list I_h) : option (list oid) :=
    match ys with
    | [] => Some []
    | Ih_Object C' o :: tl =>
        if String.eqb C' C then
          match go tl with
          | Some os => Some (o :: os)
          | None => None
          end
        else None
    | _ :: _ => None
    end
  in go xs.

  (**
  ra_rows_oids C rows
  从关系代数的行集合中提取属于类 C 的对象标识符。
  每一行 r 必须在列 val_col 上包含：
      Ira_Object C o

  语义：
  - 每行必须在 val_col 列上是对象值
  - 且对象类名必须等于 C
  - 否则返回 None

  成功时返回：
      Some [o1; o2; ...; on]

  这是 RA 表示 → OCL 对象 bag 的反向投影：

      list RowData  →  option (list oid)

  用于证明：
      RA 编码与 OCL 语义一致
*)
Definition ra_rows_oids (C : class_name) (rows : list RowData) : option (list oid) :=
  let fix go (rs : list RowData) : option (list oid) :=
    match rs with
    | [] => Some []
    | r :: tl =>
        match lookup_row val_col r, go tl with
        | Some (Ira_Object C' o), Some os =>
            if String.eqb C' C then Some (o :: os) else None
        | _, _ => None
        end
    end
  in go rows.



  



(**
  bag_equiv_oids os1 os2

  表示两个对象标识符列表在 bag 语义下等价。

  我们采用 multiset 等价定义：
      顺序无关，但重数保留

  即：
      os1 和 os2 是同一个多重集合

  形式上用 Permutation：
      Coq 的 Permutation 正好刻画 bag 等价。
*)
Definition bag_equiv_oids (os1 os2 : list oid) : Prop :=
  Permutation os1 os2.

(**
  ocl_ra_inv_res_ok C ocl_ie rows

  OCL ↔ RA 结果一致性的核心不变量。

  这个谓词描述：
      一个 OCL 表达式求值得到的 bag 结果
  与
      关系代数执行得到的行集合

  在对象语义层面是等价的。

  ----------------------------------------
  语义解释
  ----------------------------------------

  假设：

      ocl_ie  : OCL 结果值
      rows    : RA 查询结果
      C       : 对象类

  那么：

      ocl_ie 必须是 Bag(Object C)

  并且满足以下一致性条件之一：

  1. 空情况：
     OCL 空 bag  <->  RA 空结果

         xs = []  ↔  rows = []

  2. 非空情况：
     从两边提取对象 oid 后，
     它们在 multiset 语义下等价：

         bag_equiv_oids

  ----------------------------------------
  直观理解

  这个不变量说的是：

      OCL 的对象 bag
  和
      RA 的行集合

  表示的是同一组对象，
  只是编码方式不同。

  它是 OCL → RA 语义等价证明的核心桥梁。

  ----------------------------------------
  用途

  这个定义将在证明中反复出现：

  - 选择（select）
  - 聚合（aggregate）
  - 连接（join）
  - 全实例（allInstances）
  - 迭代器语义

  每一步都保持这个不变量成立。
*)
Definition ocl_ra_inv_res_ok
  (C : class_name)
  (ocl_ie : I_e)
  (rows : list RowData)
  : Prop :=
  exists xs,
    ocl_ie = Ie_Bag (Th_Object C) xs /\
    (
      (* 空 bag <-> rows 空 *)
      (xs = [] /\ rows = [])
      \/
      (* 非空：提取 oid 后做 multiset 等价 *)
      (xs <> [] /\
       exists oids1 oids2,
         ocl_obj_bag_oids C xs = Some oids1 /\
         ra_rows_oids C rows    = Some oids2 /\
         bag_equiv_oids oids1 oids2)
    ).







(**
  Lemma allInstances_only_objects

  语义性质：
  -------------------------
  OCL 的 allInstances(C) 只会产生类 C 的对象。

  换句话说：
      allInstances 不会混入其它类的对象，
      也不会产生非对象值。

*)
Lemma allInstances_only_objects :
  forall M SS E C Th deps xs,
    cevalR M SS E (CAllInstances C) {| val_val := Ie_Bag Th xs; val_deps := deps |} ->
    Th = Th_Object C /\
    Forall (fun x => exists o, x = Ih_Object C o) xs.
Proof.
  intros M SS E C Th deps xs H.
  inversion H; subst.
  (* 现在目标应该已经变成了 Th_Object C 和 xs = map ... 这种形状 *)

  split.
  - reflexivity.
  - (* xs 是 map (Ih_Object C) oids *)
    (* 证明 Forall (fun x => exists o, x = Ih_Object C o) (map ...) *)
    induction oids as [|o tl IH]; simpl.
    + constructor.
    + constructor.
      * exists o. reflexivity.
      * clear - tl C.
        induction tl as [|o tl IH]; simpl.
        -- constructor.
        -- constructor.
          ++ exists o. reflexivity.
          ++ exact IH.
Qed.




(**
  Lemma select_out_in

  语义性质（安全性 / “不产生新元素”）：
  ----------------------------------------
  对于 OCL 的 iterator 语义 E_Select（select 过滤）而言，
  输出 bag `out` 中的每个元素都必须来自输入 bag `xs`。

      out ⊆ xs   （在 list 的元素包含意义下）

  注意：这里我们证明的是 *集合包含*（subset），
  不涉及顺序，也不涉及 multiplicity 的精确保持（那是更强的性质）。
*)
Lemma select_out_in :
  forall M SS E var body Th deps xs out,
    E_Select M SS E var body
      {| val_val := Ie_Bag Th xs; val_deps := deps |}
      {| val_val := Ie_Bag Th out; val_deps := deps |} ->
    (forall x, In x out -> In x xs).
Proof.
  intros M SS E var body Th deps xs out Hsel.
  dependent induction Hsel; intros x Hin; simpl in *.
  - (* Nil *)
    contradiction.
  - (* Keep *)
    simpl in Hin.
    destruct Hin as [Hx | Hin'].
    + subst. simpl. left. reflexivity.
    + simpl. right. eapply IHHsel; eauto.
  - (* Drop *)
    simpl. right. eapply IHHsel; eauto.
Qed.



(**
  Lemma combine_singleton

  结构等式：
  -------------------------
  将两个单元素列表做 combine，
  等价于生成一个单元素 pair 列表。

      combine [a] [b] = [(a,b)]

  ----------------------------------------
  语义意义

  这是 combine 在最小非空输入上的规范行为。

*)
Lemma combine_singleton :
  forall (A B : Type) (a : A) (b : B),
    combine [a] [b] = [(a,b)].
Proof. reflexivity. Qed.



(**
  Lemma lookup_row_single

  单元素行查找的规范行为。

  ----------------------------------------
  语义说明

  对只包含一列的行：

      [(c', v)]

  在列 c 上做 lookup 的结果是：

      Some v   若 c = c'
      None     若 c ≠ c'

  即：

      lookup_row c [(c', v)]
      = if c =? c' then Some v else None

  这个 lemma 给出了 lookup_row 在最小输入上的精确规格，
  是后续行语义推理中的基础 rewrite 规则。

*)
Lemma lookup_row_single :
  forall (c c' : ColName) (v : I_ra),
    lookup_row c [(c', v)] = if c =? c' then Some v else None.
Proof.
  intros. simpl. destruct (string_dec c' c) as [Heq | Hneq].
- subst.
  (* 目标变成: Some v = if c =? c then Some v else None *)
  rewrite String.eqb_refl.
  reflexivity.
- (* c' <> c *)
  (* 目标: None = if c =? c' then Some v else None *)
  assert (Hneq' : c <> c').
  { intro Hcc'. apply Hneq. now symmetry. }
  (* 用 eqb_neq 得到 c =? c' = false *)
  apply String.eqb_neq in Hneq'.
  rewrite Hneq'.
  reflexivity.
Qed.






(**
  Lemma project_rowR_single_self_lookup

  单列投影的正确性（self → val_col）。

  ----------------------------------------
  语义说明

  若对一行 r 做如下投影：

      [ val_col := self ]

  得到新行 r'，

  那么 r' 在 val_col 上的值，
  必须等于 r 在 "self" 列上的值：

      lookup_row val_col r'
      = lookup_row "self" r

  这说明：

      project 只是重命名/复制列，
      不改变值本身。

  ----------------------------------------
*)
Lemma project_rowR_single_self_lookup :
  forall (SC : Schema) (DB : DBInstance SC) (r r' : RowData),
    project_rowR SC DB [mkProj val_col (RCol "self")] r r' ->
    lookup_row val_col r' = lookup_row "self" r.
Proof.
  intros SC DB r r' Hpr.
  inversion Hpr as [DB0 ps0 r0 vs Hnodup Hf2]; subst.
  (* 现在：
       ps0 = [mkProj val_col (RCol "self")]
       r'  = combine (map fst ps0) vs
       Hf2 : Forall2 (fun p v => evalRexR SC DB r (snd p) v) ps0 vs
  *)
  simpl in Hnodup. (* NoDup [val_col] *)
  (* Forall2 单元素反演 *)
  inversion Hf2 as [|p v ps vs' Hev Hf2' Hvs]; subst.
  inversion Hf2' ; subst.  (* 让尾部变成 [] *)

  (* 此时 ps0 = [(val_col, RCol "self")]，vs = [v]，且 Hev : evalRexR SC DB r (RCol "self") v *)

  (* 用 evalRexR 的列求值规则把 v 与 lookup_row "self" r 关联起来 *)
  inversion Hev; subst.
  (* 若你的列规则是 ER_Col : lookup_row cn row = Some v -> evalRexR ... (RCol cn) v *)

  (* 现在 r' = combine [val_col] [v] = [(val_col,v)] *)
  simpl. symmetry. exact H2.
Qed.





(**
  Lemma project_rowsR_single_self_lookup_hd

  行列表投影的头元素正确性。

  ----------------------------------------
  语义说明

  对行列表执行：

      project [val_col := self]

  如果：

      (r :: rs)  ↦  (r' :: rs')

  那么头行 r' 的 val_col 列，
  必须等于原头行 r 的 "self" 列：

      lookup_row val_col r'
      = lookup_row "self" r

  也就是说：

      投影对每一行逐点生效，
      且保持 self 列的值。

  ----------------------------------------
*)

(* Lemma project_rowsR_single_self_lookup_hd :
  forall (SC : Schema) (DB : DBInstance SC) (r r' : RowData) rs rs',
    project_rowsR SC DB [mkProj val_col (RCol "self")] (r :: rs) (r' :: rs') ->
    lookup_row val_col r' = lookup_row "self" r.
Proof.
  intros SC DB r r' rs rs' Hprs.
  inversion Hprs; subst.
  eapply project_rowR_single_self_lookup; eauto.
Qed. *)





(**
  goRow C rs

  从行列表 rs 的 val_col 列中提取
  属于类 C 的对象标识符列表。

  ----------------------------------------
  语义说明

  对每一行 r：

    1. 在 val_col 上 lookup
    2. 必须得到对象值 Ira_Object C' o
    3. 且 C' 必须等于目标类 C

  若所有行都满足条件：

      Some [o1; o2; ...; on]

  否则：

      None

  ----------------------------------------
  失败条件

  - 某行 val_col 不是对象
  - 或对象类 ≠ C
  - 或递归子结果失败

  整体返回 None。
*)
Definition goRow (C : class_name) (rs : list RowData) : option (list oid) :=
  let fix go (rs : list RowData) : option (list oid) :=
    match rs with
    | [] => Some []
    | r :: tl =>
        match lookup_row val_col r with
        | Some (Ira_Object C' o0) =>
            match go tl with
            | Some os0 => if C' =? C then Some (o0 :: os0) else None
            | None => None
            end
        | _ => None
        end
    end
  in go rs.

(**
  goSelf C rs

  与 goRow 相同，但从 "self" 列提取对象。
*)
Definition goSelf (C : class_name) (rs : list RowData) : option (list oid) :=
  let fix go (rs : list RowData) : option (list oid) :=
    match rs with
    | [] => Some []
    | r :: tl =>
        match lookup_row "self" r with
        | Some (Ira_Object C' o0) =>
            match go tl with
            | Some os0 => if C' =? C then Some (o0 :: os0) else None
            | None => None
            end
        | _ => None
        end
    end
  in go rs.





(**
  Lemma project_rowsR_self_go

  self 投影与对象解码的一致性。

  ----------------------------------------
  语义说明

  若对行列表 rows0 执行如下投影：

      project [val_col := self]

  得到新列表 rows，

  那么从 rows 的 val_col 列解码得到的对象 oid 列表，
  等于从 rows0 的 "self" 列解码得到的对象 oid 列表：

      goRow  C rows
    = goSelf C rows0

  这说明：

      self → val_col 的投影
      在对象语义层面是透明的。

  ----------------------------------------
  直观意义

  该 lemma 表示：

      列重命名不会改变对象语义

  它是 OCL → RA 翻译正确性的核心桥梁之一：

      表结构变了，
      但对象集合没变。

*)
(* Lemma project_rowsR_self_go :
  forall SC DB C rows0 rows,
    project_rowsR SC DB [mkProj val_col (RCol "self")] rows0 rows ->
    goRow C rows = goSelf C rows0.
Proof.
  intros SC DB C rows0 rows Hprs.
  remember [mkProj val_col (RCol "self")] as ps eqn:Hps.
  (* 现在 Hprs : project_rowsR ... ps rows0 rows *)
  revert Hps.
  induction Hprs; intros Hps; subst ps.
  - (* PR_nil *) reflexivity.
  - (* PR_cons *)
    simpl.

    (* 反演 project_rowR，取出单投影产生的 v，以及 r' 的形状 *)
    inversion H; subst.
    (* 得到：Forall2 ... [mkProj val_col (RCol "self")] [v] 以及 r' = combine ... *)
    inversion H1; subst.  (* H1 是 Forall2 那个前提，名字按你实际为准 *)
    (* 你当前上下文里：IHHprs, Hprs, H, H1, H4, H6 ... *)

    (* 0) 先把 IH 实例化出来：它需要一个等式参数 *)
    pose proof (IHHprs eq_refl) as IH.  (* IH : goRow C rs' = goSelf C rs *)

    (* 1) 由 Forall2 [] l' 可推出 l' = [] *)
    inversion H6; subst.  (* l' = [] *)

    (* 2) H4: evalRexR ... (RCol "self") y 反演出 lookup_row "self" r = Some y *)
    (* snd (mkProj ...) = RCol "self" 已经在 H4 里了 *)
    inversion H4; subst.
    (* 现在你会得到类似：Hself : lookup_row "self" r = Some y （名字以实际为准） *)
    rename H0 into Hself.  (* 如果你的名字不是 H0，请改成你真实的那个假设名 *)

    (* 3) 左边的 combine/map fst/lookup_row 化简成 Some y *)
    simpl (map fst [mkProj val_col (RCol "self")]).
    (* 得到: map fst [...] = [val_col] *)
    simpl (combine [val_col] (y :: [])).
    (* 得到: combine ... = [(val_col,y)] *)
    simpl (lookup_row val_col ((val_col, y) :: [])).
    (* 得到: if string_dec val_col val_col then Some y else ... *)
    destruct (String.string_dec val_col val_col) as [_|Hneq]; [|contradiction].
    (* 右边先用 H7 把 lookup_row "self" r 改成 Some y *)
    rewrite H7.

    (* 再用 IH 把 goSelf C rs 改成 goRow C rs'（或反过来都行） *)
    rewrite <- IH.
    (* 现在目标应该变成：
      match y with ... goRow C rs' ... = match Some y with ... goRow C rs' ...
    *)

    (* 让右边的 match Some y 展开 *)
    simpl.

    (* 对 y 分类讨论即可 *)
    destruct y; simpl; try reflexivity.
    Qed. *)



(* option 返回值的函数性 *)
Lemma option_Some_inj {A} (x y : A) :
  Some x = Some y -> x = y.
Proof. intro H; inversion H; reflexivity. Qed.


(* scalar_extract 的确定性 *)
Lemma scalar_extract_det :
  forall cn rows v1 v2,
    scalar_extract cn rows = Some v1 ->
    scalar_extract cn rows = Some v2 ->
    v1 = v2.
Proof.
  intros cn rows v1 v2 H1 H2.
  rewrite H1 in H2. inversion H2. reflexivity.
Qed.












Lemma Forall2_pointwise_det
  (A B : Type) (R : A -> B -> Prop) :
  (forall a b1 b2, R a b1 -> R a b2 -> b1 = b2) ->
  forall xs ys1 ys2,
    Forall2 R xs ys1 ->
    Forall2 R xs ys2 ->
    ys1 = ys2.
Proof.
  intros Hdet xs ys1 ys2 H1.
  revert ys2.
  induction H1; intros ys2 H2.
  - inversion H2; subst; reflexivity.
  - inversion H2; subst.
    specialize (Hdet x y y0 H H4). subst y0.
    f_equal. eapply IHForall2 ; eauto.
Qed.





(* 
evalRelR_det 依赖select_rowsR_det，project_rowsR_det，cartesian_rowsR_det 
evalRexR_det依赖evalRelR_det 
project_rowR_det依赖evalRexR_det 
cartesian_rowR_det依赖 无 
select_rowsR_det依赖evalRexR_det 
project_rowsR_det依赖project_rowR_det 
cartesian_rowsR_det依赖cartesian_rows_oneR_det 
cartesian_rows_oneR_det依赖cartesian_rowR_det
*)



Lemma cartesian_rowR_det :
  forall SC (DB : DBInstance SC) r1 r2 out1 out2,
    cartesian_rowR SC DB r1 r2 out1 ->
    cartesian_rowR SC DB r1 r2 out2 ->
    out1 = out2.
Proof.
  intros SC DB r1 r2 out1 out2 Hc1 Hc2.
  inversion Hc1. subst.
  inversion Hc2. subst. 
  (* 两边输出都是 row_merge r1 r2 *)
  reflexivity.
Qed.





Lemma cartesian_rows_oneR_det :
  forall SC (DB : DBInstance SC) r1 rows2 out1 out2,
    cartesian_rows_oneR SC DB r1 rows2 out1 ->
    cartesian_rows_oneR SC DB r1 rows2 out2 ->
    out1 = out2.
Proof.
  intros SC DB r1 rows2 out1 out2 Hc1.
  revert out2.
  induction Hc1; intros out2 Hc2.
  - inversion Hc2. reflexivity.
  - inversion Hc2.
    f_equal.
    + eapply cartesian_rowR_det; eauto.
    + eauto.
Qed.






Lemma cartesian_rowsR_det :
  forall SC (DB : DBInstance SC) rows1 rows2 out1 out2,
    cartesian_rowsR SC DB rows1 rows2 out1 ->
    cartesian_rowsR SC DB rows1 rows2 out2 ->
    out1 = out2.
Proof.
  intros SC DB rows1 rows2 out1 out2 Hc1.
  revert out2.
  induction Hc1; intros out2 Hc2.
  - inversion Hc2. reflexivity.
  - inversion Hc2.
    (* out1 = out1_0 ++ outRest, out2 = out1_1 ++ outRest0 *)
    pose proof (cartesian_rows_oneR_det SC DB r1 rows2 out1 out0 H H3) as ->.
    pose proof (IHHc1 _ H6) as ->.
    reflexivity.
Qed.
















(* ------------------------------------------------------------ *)
(* Determinism for the mutually recursive big-step semantics      *)
(* ------------------------------------------------------------ *)

Lemma evalRelR_det :
  forall SC (DB : DBInstance SC) q rows1 rows2,
    evalRelR SC DB q rows1 ->
    evalRelR SC DB q rows2 ->
    rows1 = rows2

with evalRexR_det :
  forall SC (DB : DBInstance SC) row e v1 v2,
    evalRexR SC DB row e v1 ->
    evalRexR SC DB row e v2 ->
    v1 = v2

with project_rowR_det :
  forall SC (DB : DBInstance SC) ps r r1 r2,
    project_rowR SC DB ps r r1 ->
    project_rowR SC DB ps r r2 ->
    r1 = r2

with select_rowsR_det :
  forall SC (DB : DBInstance SC) cond rows out1 out2,
    select_rowsR SC DB cond rows out1 ->
    select_rowsR SC DB cond rows out2 ->
    out1 = out2.


Proof.

  (* ======================== evalRelR_det ======================== *)
  -
    intros SC DB q rows1 rows2 H1 H2.
    revert rows2 H2.
    induction H1; intros rows2' H2.

    + inversion H2; subst. reflexivity.
    + inversion H2; subst. reflexivity.
    + inversion H2; subst.

      rewrite H in H3. inversion H3. reflexivity.

    + (* ER_Select *)
      inversion H2; subst.

      (* 先把子查询 q 的 rows 对齐 *)
      pose proof (IHevalRelR _ H5) as ->.
      (* 再用 select_rowsR 的确定性对齐 rows' *)
      eapply select_rowsR_det; eauto.

    + (* ER_Project *)
      inversion H2; subst.
      pose proof (IHevalRelR _ H5) as ->.
      (* 现在有：
        H  : Forall2 (project_rowR SC DB ps) rows0 rows'
        H7 : Forall2 (project_rowR SC DB ps) rows0 rows2'
        目标 rows' = rows2'
      *)
      eapply (Forall2_pointwise_det RowData RowData (project_rowR SC DB ps)).
      -- intros a b1 b2 Hb1 Hb2.
        eapply project_rowR_det; eauto.
      -- exact H.
      -- exact H7.


    + (* ER_Cartesian *)
      inversion H2; subst.
      pose proof (IHevalRelR1 _ H3) as ->.
      pose proof (IHevalRelR2 _ H5) as ->.
      eapply cartesian_rowsR_det; eauto.

    + (* ER_Join *)
      inversion H2; subst.
      pose proof (IHevalRelR1 _ H5) as ->.
      pose proof (IHevalRelR2 _ H7) as ->.
      (* 笛卡尔积输出确定 *)
      pose proof (cartesian_rowsR_det SC DB rows0 rows3 rowsCart rowsCart0 H H9) as ->.
      (* select 输出确定 *)
      eapply select_rowsR_det; eauto.

    + (* ER_Union *)
      inversion H2; subst.
      pose proof (IHevalRelR1 _ H3) as ->.
      pose proof (IHevalRelR2 _ H5) as ->.
      reflexivity.

    + (* ER_Diff *)
      inversion H2; subst.
      pose proof (IHevalRelR1 _ H3) as ->.
      pose proof (IHevalRelR2 _ H5) as ->.
      (* rows' 由等式 bag_diff_rows ... = rows' 唯一确定 *)
      reflexivity.

    + (* ER_Distinct *)
      inversion H2; subst.
      pose proof (IHevalRelR _ H3) as ->.
      reflexivity.

    + (* ER_Aggregate *)
      inversion H2; subst.
      pose proof (IHevalRelR _ H7) as ->.
      (* groups 与 rows' 都由等式唯一确定 *)
      rewrite H0 in H10. inversion H10. reflexivity.


  (* ======================== evalRexR_det ======================== *)
  - intros SC DB row e v1 v2 He1.
    revert v2.
    induction He1; intros v2' He2.
    + (* ER_Col *)
      inversion He2; subst.
      rewrite H in H3. inversion H3. reflexivity.

    + (* ER_Val *)
      inversion He2; subst. reflexivity.

    + (* ER_Unop *)
      inversion He2; subst.
      pose proof (IHHe1 _ H4) as ->.
      rewrite H6 in H. inversion H. reflexivity.

    + (* ER_Binop *)
      inversion He2; subst.
      pose proof (IHHe1_1 _ H5) as ->.
      pose proof (IHHe1_2 _ H7) as ->.
      rewrite H in H8. inversion H8. reflexivity.

    + (* ER_Subquery *)
      inversion He2; subst.
      (* 关键：子查询 evalRelR 的确定性 *)
      pose proof (evalRelR_det SC DB q rows rows0 H H5) as ->.
      (* scalar_extract 是函数：Some v = Some v2 -> v=v2 *)
      rewrite H0 in H7. inversion H7. reflexivity.

  (* ======================== project_rowR_det ======================== *)
  - intros SC DB ps r r1 r2 Hpr1 Hpr2.
    inversion Hpr1; subst. clear Hpr1.
    inversion Hpr2; subst. clear Hpr2.

    (* r1 = combine (map fst ps) vs, r2 = combine (map fst ps) vs0 *)
    (* 证明 vs=vs0：Forall2 + evalRexR_det *)
    assert (vs = vs0) as ->.
    {
      eapply (Forall2_pointwise_det (ColName * rex) I_ra (fun p v => evalRexR SC DB r (snd p) v)).
      - (* 点态确定性：这一步才用 evalRexR_det（在 mutual 内已可用） *)
        intros p v1 v2 Hp1 Hp2.
        eapply evalRexR_det; eauto.
      - exact H0.
      - exact H2.
    }
      subst. reflexivity.



  (* ======================== select_rowsR_det ======================== *)
  - intros SC DB cond rows out1 out2 Hs1.
    revert out2.
    induction Hs1; intros out2 Hs2.
    + inversion Hs2. reflexivity.
    + (* keep *)
      inversion Hs2.
      * f_equal.
        -- exact (IHHs1 _ H6).
      * pose proof (evalRexR_det SC DB r cond (Ira_Bool true) (Ira_Bool false) H H4) as Heq.
        discriminate.
    + (* drop_false *)
      inversion Hs2.
      * pose proof (evalRexR_det SC DB r cond (Ira_Bool false) (Ira_Bool true) H H4) as Heq.
        discriminate.
      * exact (IHHs1 _ H6).



Qed.





(* ------------------------------------------------------------ *)
(* The theorem you asked for: just pick the first two lemmas     *)
(* ------------------------------------------------------------ *)
Theorem evalRelR_evalRexR_det :
  (forall SC (DB : DBInstance SC) q rows1 rows2,
      evalRelR SC DB q rows1 ->
      evalRelR SC DB q rows2 ->
      rows1 = rows2)
  /\
  (forall SC (DB : DBInstance SC) row e v1 v2,
      evalRexR SC DB row e v1 ->
      evalRexR SC DB row e v2 ->
      v1 = v2).
Proof.
  split.
  - exact evalRelR_det.
  - exact evalRexR_det.
Qed.


















