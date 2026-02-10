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
(* Lemma allInstances_only_objects :
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
Qed. *)




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
(* Lemma select_out_in :
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
Qed. *)



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
(* Lemma project_rowR_single_self_lookup :
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
Qed. *)





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


















(**
  Theorem inv_semantic_preservation

  OCL 不变量语义 → 关系代数执行语义 保持定理

  ======================================================
  语义陈述
  ======================================================

  对任意：

      object model      M
      system state      SS
      schema            SC
      database          DB
      class             C
      invariant expr    expr

  若：

  1) schema 与 object model 一致
         EncSchemaW M SC

  2) database 编码正确
         EncDBW M SS SC DB

  3) OCL 语义求值成功
         cevalR ... (inv_tm C expr) vb

     即：
         class.allInstances
         → select(self | not expr)

     产生 OCL 结果 vb

  4) 翻译成功
         translate ... = Some (Rel ra, ...)

  5) RA 执行成功
         evalRelR ... ra rows

  ------------------------------------------------------

  则：

      OCL 结果 与 RA 结果语义一致

      ocl_ra_inv_res_ok C (val_val vb) rows

  ======================================================
  直观意义
  ======================================================

  这说明：

      OCL 不变量检查
      =
      SQL / 关系代数查询

  在语义层面完全等价。

  换句话说：

      编译器没有改变语义。

  这是一个标准的：

      semantic preservation theorem
      编译正确性定理
*)
(* Theorem inv_semantic_preservation
  (M  : object_model)
  (SS : system_state M)
  (SC : Schema)
  (DB : DBInstance SC)
  (C  : class_name)
  (expr : tm)
  (E : env)
  (vb : val_b)
  (ra : rel)
  (vl : list var_name)
  (te : T_e)
  (dim : rel)
  (rows : list RowData)
  :
  EncSchemaW M SC ->
  EncDBW M SS SC DB ->
  (* 1) OCL 求值：class.allInstances->select(self | not expr) 产生 vb *)
  cevalR M SS E (inv_tm C expr) vb ->
  (* 2) 翻译成功，且翻译出来是 Rel ra *)
  translate M empty (inv_tm C expr) = Some (Rel ra, vl, te, dim) ->
  (* 3) RA 求值 *)
  evalRelF SC DB ra rows ->
  (* 4) 结果对应：空则空；非空则元素 multiset 相同 *)
  ocl_ra_inv_res_ok C (val_val vb) rows.
Proof.
  intros HEncSc HEncDB Hceval Htr HevalRA.
  (* 1) 展开 inv_tm，确保最外层能看到 CSelect *)
  unfold inv_tm in *.

  (* 2) 对 OCL 的求值推导做反演：应该命中 E_CSelect *)
  inversion Hceval. subst.
  (* 此处你会得到类似这些前提（名字以 inversion 结果为准）：
       - cevalR ... t {| val_val := Ie_Bag Th xs; val_deps := deps |}
       - E_Select ... var body ... out
     以及 vb = {| val_val := Ie_Bag Th out; val_deps := deps |}
  *)

  (* 3) 对翻译结果做结构化化简：translate 的 CSelect 分支 *)
  (*    这里用 rewrite/ simpl in Htr, 然后 destruct translate ... *)
  simpl in Htr.
  (* 如果 simpl 不够，就继续把 inv_tm 展开到 CSelect 的具体项 *)

  destruct (lookup_class M C) eqn:Hlc; try discriminate.

  (* 关键：把中间 translate 的结果单独拿出来 *)
  remember
    (translate M
      (update empty "self"
          (RAProject [mkProj val_col (RCol oid_col)] (RATable C),
          [], Th_Object C)) expr)
    as tr_self eqn:Htr_self.

  destruct tr_self as [[[[k vl0] te0] dim0] | ] eqn:Hcase; try discriminate.

  destruct k as [e1 | rel0].
  - (* k = Rex e1 *)
    (* 这条必然无法产生外层所需的 Some (Rel ...) *)
    simpl in Htr.
    (* 先把 Htr 里“内层 match vl0/dim0/te0”的结果算出来 *)
    destruct vl0 as [|v vl0']; simpl in Htr; try discriminate.
    destruct dim0; simpl in Htr; try discriminate.
    destruct te0 as [th0 | th0]; simpl in Htr; try discriminate.
    destruct th0 as [tb0 | c0]; simpl in Htr; try discriminate.
    destruct tb0; simpl in Htr; try discriminate.

  - (* k = Rel rel0 *)
    simpl in Htr.

    (* 1) 先从 Htr 推出 dim0 必须是 RAEmpty，否则内层 match = None *)
    destruct dim0; simpl in Htr; try discriminate.
    (* 此时 dim0 已经被替换成 RAEmpty *)

    (* 2) 再从 Htr 推出 te0 必须是 Te_Single (Th_Basic Tb_Bool) *)
    destruct te0 as [th0 | th0]; simpl in Htr; try discriminate.
    destruct th0 as [tb0 | c0]; simpl in Htr; try discriminate.
    destruct tb0; simpl in Htr; try discriminate.
    (* 到这里 tb0 只能是 Tb_Bool，其他都会导致 None = Some ... *)

    (* 3) 现在内层 match 已经化简成 Some (Rel (...), vl0, Te_Single Bool, RAEmpty)
          外层 match 也会命中第一个分支，Htr 会变成一个明确的 Some = Some *)
    inversion Htr; subst.
    (* 你会得到：
      - ra = RAProject [mkProj val_col (RCol "self")] (RASelect ... rel2)
      - vl = []
      - te = Te_Bag (Th_Object C)
      - dim = RAEmpty
      同时 rel2 = (RAProject (proj_cols [] ++ ...) rel0) 之类的具体形式
    *)

    clear Htr.

    remember (RAProject [mkProj val_col (RCol "self")]
    (RASelect (RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true)))
      (RAProject (proj_cols vl0 ++
          [mkProj val_col (RUnop (U_Bool UNot) (RCol val_col))]) rel0)))
    as ra_inv eqn:Hra_inv.
  (* 现在 HevalRA : evalRelR SC DB ra_inv rows *)

  subst ra_inv.  (* 如果你做了 remember *)
  inversion HevalRA; subst.

  (* H2 : evalRelR ... (RASelect cond inner) rows0 *)
  inversion H2; subst.
  (* 现在你应该得到：
    - rows1 : list RowData
    - HevalInner : evalRelR SC DB inner rows1
    - Hfilter : select_rowsR SC DB cond rows1 rows0
    （名字以你 inversion 实际输出为准）
  *)

  unfold ocl_ra_inv_res_ok.
  (* 如果里面还有辅助定义，比如 rows_vals / bag_elems 等，也继续 unfold。 *)
  unfold ocl_obj_bag_oids.
  unfold ra_rows_oids.
  unfold bag_equiv_oids.


  (* 1) 选 xs0 := out *)
  exists out.
  split.
  + (* 证明 Ie_Bag Th out = Ie_Bag (Th_Object C) out *)
    (* 关键：证明 Th = Th_Object C *)
    assert (HTh : Th = Th_Object C).
    { (* 从 allInstances / select 的推导里反演出来 *)
      (* 通常 inversion H5 会暴露出 allInstances 的返回类型 *)
      inversion H5; subst; try reflexivity.
      (* 如果 H5 反演还不够，就 inversion Hceval. subst. 然后再 inversion 得到 allInstances 子推导。 *)
    }
    subst Th. reflexivity.
  + (* 进入后半部分： out=[] /\ rows=[] \/ out<>[] /\ ... *)
    destruct out as [|h tl] eqn:Hout.
    -- left.
      split; [reflexivity|].
      (* 这里要证明 rows = [] *)

      (* 先把 rows0=[] -> rows=[] 这步写好 *)
      assert (Hproj_nil : rows0 = [] -> rows = []).
      { intro H0.
        subst rows0.
        inversion H4; subst.
        reflexivity.
      }

      (* 再去证明 rows0 = [] *) 
      assert (Hrows0_nil : rows0 = []).
      { (* 用 H8: select_rowsR cond rows1 rows0 + “cond 永假” *)
        admit.
      }
      apply Hproj_nil. exact Hrows0_nil.
    -- right.
      split.
       discriminate.  (* out <> [] *)

      destruct (allInstances_only_objects _ _ _ _ _ _ _ H5) as [HTh HForall_xs].
      (* HTh : Th = Th_Object C *)
      (* HForall_xs : Forall (fun x => exists o, x = Ih_Object C o) xs *)

      assert (Hin_xs : In h xs).
      { (* out=h::tl，所以 h ∈ out；再用 select_out_in 推到 xs *)
        subst out. (* 或 rewrite Hout in ... *)
        apply (select_out_in _ _ _ _ _ _ _ _ _ H6).
        simpl. left. reflexivity.
      }

      (* 把 Forall 变成 forall x, In x xs -> ... *)
      pose proof (proj1 (@Forall_forall _ 
                        (fun x : I_h => exists o : oid, x = Ih_Object C o) 
                        xs) HForall_xs) as Hxs.
      (* Hxs : forall x : I_h, In x xs -> exists o : oid, x = Ih_Object C o *)

      specialize (Hxs h Hin_xs).
      destruct Hxs as [o Ho].
      subst h.

      rewrite (String.eqb_refl C).


      assert (HForall_out :
        Forall (fun x:I_h => exists o:oid, x = Ih_Object C o) (Ih_Object C o :: tl)).
      {
        (* 用 HForall_xs + H6 推出来：对 H6 做 induction *)
        (* 结构大概是：induction H6; constructor; eauto; ... *)
        admit.
      }
      inversion HForall_out as [| ? ? Hhd Htl]. subst.
      (* 得到：Htl : Forall (fun x => exists o, x = Ih_Object C o) tl *)


      (* 1) 给 I_h 的 go 起个名字，避免反复展开 *)
      set (goIh :=
        (fix go (ys : list I_h) : option (list oid) :=
          match ys with
          | [] => Some []
          | Ih_Basic _ :: _ => None
          | Ih_Object C' o0 :: tl0 =>
              if C' =? C then
                match go tl0 with
                | Some os => Some (o0 :: os)
                | None => None
                end
              else None
          end)).

      (* 2) 证明：tl 中全是 Ih_Object C _ -> goIh tl = Some os *)
      assert (Hex_os : exists os, goIh tl = Some os).
      {
        clear -Htl.  (* 只留 Forall 前提，别让上下文干扰归纳 *)
        induction tl as [|h tl' IH]; simpl.
        - exists []; reflexivity.
        - inversion Htl as [|x xs Hx Hxs]. subst.
          destruct Hx as [o0 Ho0]. subst.
          (* 现在 head 一定是 Ih_Object C o0 *)
          (* 展开 goIh 在 cons 情况 *)
          simpl.
          (* 这里会出现 if (C =? C) then ... else ...，用 eqb_refl 化简 *)
          rewrite String.eqb_refl.
          destruct (IH Hxs) as [os Hos].
          rewrite Hos.
          exists (o0 :: os). reflexivity.
      }

      destruct Hex_os as [os Hos].




      (* 用 Hos 解决左边 match *)
      exists (o :: os).

      (* 1) 先处理 goIh 这一半 *)
      rewrite Hos.  (* 把 match goIh tl ... 变成 Some (o::os) *)

      (* 2) 把 oids2 取成 goRow rows 的结果 *)
      destruct (goRow C rows) as [l|] eqn:Hgo.


      ++ (* goRow rows = Some l *)
        exists l.
        repeat split.
        (* 目标：Permutation (o :: os) l *)

        (* 1) 从 project 把 goRow rows 变成 goSelf rows0 *)
        assert ( Hproj : goRow C rows = goSelf C rows0).
        { eapply project_rowsR_self_go; eauto. }   (* 需要你刚才那个列表级 lemma *)

        rewrite Hgo in Hproj.  (* Some l = goSelf C rows0 *)

        (* 2) 证明 goSelf C rows0 = Some (o :: os) *)
        assert ( Hself : goSelf C rows0 = Some (o :: os)).
        {
          unfold goSelf.

          (* 1) 先把 rows0 的结构暴露出来：因为 out 非空，rows0 也必须非空
            这一点通常需要一个“长度保持/非空保持”的小引理：
            - OCL select out = o::tl -> exists r0 rs0, rows0 = r0::rs0
            这个引理的证明会用到你整体证明里“allInstances 对应表/行”的桥梁。 *)

          destruct rows0 as [| r0 rs0] eqn:Hrows0.
          - (* rows0 = [] 会导致 goSelf = Some []，不可能等于 Some (o::os) *)
            (* 这里用你后面最终要的 Permutation 也能推出矛盾，但更推荐直接用 o::os 非空 *)
            eauto.
          - (* rows0 = r0 :: rs0 *)
            simpl.

          (* 2) 对 H8 : select_rowsR ... rows1 rows0 反演到 SR_keep/SR_drop_false *)
          inversion H8; subst.
            (* 只可能是 SR_keep 产生 r0::rs0，
              得到：
                Hevcond : evalRexR ... r0 cond (Ira_Bool true)
                H8_tail : select_rowsR ... rows1_tail rs0
            *)

          (* 3) 从 Hevcond 推出 r0 的 val_col=true，于是它对应的 self=oid 必须是 o
            这一步需要你已经证明的“allInstances 对应 rows1 的顺序”桥梁，
            再用 row_notexpr_true_iff_valcol_true 的逆向方向把 OCL 的第一个 keep 元素就是 o。 *)

          (* 4) 对 tail 用归纳假设，得到 goSelf C rs0 = Some os *)
          (* 这里 tail 的 os 来自 Hos : goIh tl = Some os 与 OCL E_Select 的递归结构对齐 *)

          (* 5) 最后拼起来：goSelf (r0::rs0) = Some (o::os) *)

        }

        (* 3) 合并得到 l = o::os *)
        rewrite Hself in Hproj.
        inversion Hproj; subst.

        (* 4) 收尾 *)
        apply Permutation_refl. *)
