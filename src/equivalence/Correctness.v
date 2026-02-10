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















Lemma select_rowsF_in_true :
  forall evalRex cond rows1 rows2 r,
    select_rowsF evalRex cond rows1 = Some rows2 ->
    In r rows2 ->
    In r rows1 /\
    evalRex r cond = Some (Ira_Bool true).
Proof.
  intros evalRex cond rows1.
  induction rows1 as [|x xs IH]; intros rows2 r Hsel Hin.
  - simpl in Hsel. inversion Hsel; subst rows2. contradiction.
  - simpl in Hsel.
    destruct (evalRex x cond) as [vc|] eqn:Hc; try discriminate.
    destruct vc; try discriminate.
    destruct b.
    + (* true: keep x *)
      destruct (select_rowsF evalRex cond xs) as [out|] eqn:Hrec; try discriminate.
      inversion Hsel; subst rows2; clear Hsel.
      simpl in Hin.
      destruct Hin as [-> | Hin'].
      * split; [left; reflexivity | exact Hc].
      * destruct (IH out r eq_refl Hin') as [Hin_xs Hr_true].
      split.
      -- right. exact Hin_xs.
      -- exact Hr_true.

    + (* false: drop x *)
      destruct (select_rowsF evalRex cond xs) as [out|] eqn:Hrec; try discriminate.
      inversion Hsel; subst rows2; clear Hsel.
      destruct (IH out r eq_refl Hin) as [Hin_xs Htrue].
      split.
      -- right. exact Hin_xs.
      -- exact Htrue.

Qed.








Lemma select_rowsF_in :
  forall (evalRex : RowData -> rex -> option I_ra)
         (cond : rex) (rows out : list RowData) (r : RowData),
    select_rowsF evalRex cond rows = Some out ->
    In r out ->
    In r rows /\ evalRex r cond = Some (Ira_Bool true).
Proof.
  intros evalRex cond rows.
  induction rows as [|a rs IH]; intros out r Hsel Hin.
  - simpl in Hsel. inversion Hsel. subst out. contradiction.
  - simpl in Hsel.
    destruct (evalRex a cond) eqn:Ha; try discriminate.
    destruct i; try discriminate.
    destruct b.
    + destruct (select_rowsF evalRex cond rs) eqn:Hrs; try discriminate.
      inversion Hsel; subst out.
      simpl in Hin. destruct Hin as [->|Hin'].
      * split; [left; reflexivity| exact Ha].
      * specialize (IH l r eq_refl Hin') as [Hin_rs Hev].
        split.
        -- right; exact Hin_rs.
        -- exact Hev.
    + destruct (select_rowsF evalRex cond rs) eqn:Hrs; try discriminate.
      inversion Hsel; subst out.
      specialize (IH l r eq_refl Hin) as [Hin_rs Hev].
      split.
      -- right; exact Hin_rs.
      -- exact Hev.
Qed.





Lemma selectF_nil_all_false :
  forall (M : object_model) (SS : system_state M)
         (eval : env -> tm -> option val_b)
         (E : env) (var : string) (body : tm)
         (Th : T_h) (deps : list dep) (xs : list I_h),
    selectF M SS eval E var body Th deps xs = Some [] ->
    forall ih,
      In ih xs ->
      exists vb,
        eval (update E var (mk_var_b ih deps)) body = Some vb /\
        val_val vb = Ie_Single (Ih_Basic (Ib_Bool false)).
Proof.
  intros M SS eval E var body Th deps xs Hsel.
  induction xs as [|a tl IH]; intros ih Hin.
  - inversion Hin.
  - simpl in Hsel.
    (* 拆 eval (update ...) body *)
    destruct (eval (update E var (mk_var_b a deps)) body) as [vb|] eqn:Ha; try discriminate.
    (* 拆 vb 的值形状 *)
    destruct (val_val vb) as [v_single|Th' xs'] eqn:Hvv; try discriminate.
    (* v_single 必须是 Bool true/false 才可能继续 *)
    destruct v_single as [ihb|C0 o0]; try discriminate.
    destruct ihb as [b | z | r | s].
    -- (* ihb = Ib_Bool b *)
      destruct b.
      + (* b = true *)
        (* Hsel : option_map (a::) (selectF ... tl) = Some []  矛盾 *)
        simpl in Hsel. discriminate.
      + (* b = false *)
        (* Hsel : selectF ... tl = Some [] *)
        simpl in Hsel.
        (* 现在用 Hin 分析 ih 在 a::tl 里 *)
        simpl in Hin. destruct Hin as [-> | Hin_tl].
        * exists vb. split; [exact Ha|].
          (* 目标 val_val vb = ... false *)
          (* Hvv : val_val vb = Ie_Single (Ih_Basic (Ib_Bool false)) 在这个分支里应可由 Hvv 得到 *)
          (* 先把 Hvv 里的 ihb 替换掉： *)
          discriminate Hsel.
        * (* ih ∈ tl *)
          discriminate Hsel.
      + (* ihb = Ib_Int z *)
        simpl in Hsel. discriminate.
    -- (* ihb = Ib_Real r *)
      simpl in Hsel. discriminate.
    -- (* ihb = Ib_String s *)
      destruct r.
      --- (* r = true *)
        unfold option_map in Hsel.
        destruct (selectF M SS eval E var body Th deps tl) as [out_tl|] eqn:Htl;
        simpl in Hsel.
        ---- (* Hsel : Some (a :: out_tl) = Some [] *)
          discriminate Hsel.
        ---- (* Hsel : None = Some [] *)
          discriminate Hsel.
      --- (* r = false *)
        simpl in Hsel.
        simpl in Hin. destruct Hin as [Heq | Hin_tl].
        + subst ih.
          exists vb. split; [exact Ha|].
          (* 由 Hvv 得到 val_val vb = ... false *)
          exact Hvv.
        + (* ih ∈ tl *)
          eapply IH; eauto.
    -- (* ihb = Ih_Object (C0) o0 *)
      simpl in Hsel. discriminate. 
Qed.





Lemma project_rowsF_Forall2_eq
  (evalRex : RowData -> rex -> option I_ra)
  (ps : list (ColName * rex))
  (rows out : list RowData) :
  project_rowsF evalRex ps rows = Some out ->
  Forall2 (fun r r' => project_rowF evalRex ps r = Some r') rows out.
Proof.
  revert out.
  induction rows as [|r rs IH]; intros out H.
  - cbn in H. inversion H; subst. constructor.
  - cbn in H.
    destruct (project_rowF evalRex ps r) as [r'|] eqn:Hr; try discriminate.
    destruct (project_rowsF evalRex ps rs) as [out'|] eqn:Hrs; try discriminate.
    inversion H; subst.
    constructor; auto.
Qed.







Lemma project_rowsF_nil :
  forall evalRex ps rows,
    project_rowsF evalRex ps rows = Some [] ->
    rows = [].
Proof.
  intros evalRex ps rows.
  destruct rows as [|r rs]; simpl; intros H; auto.
  (* r::rs 情况下一般不可能返回 Some []，看定义：要么 discriminate，要么 inversion *)
  (* 通常： *)
  exfalso.
  (* 先把 project_rowF 和 project_rowsF 的结果拆出来 *)
  destruct (project_rowF evalRex ps r) as [r'|] eqn:Hr; simpl in H; try discriminate.
  destruct (project_rowsF evalRex ps rs) as [out|] eqn:Hrs; simpl in H; try discriminate.
Qed.


Lemma project_rowsF_on_nil :
  forall evalRex ps out,
    project_rowsF evalRex ps [] = Some out ->
    out = [].
Proof.
  intros. simpl in H. inversion H. reflexivity.
Qed.




Lemma lookup_row_cons_eq :
  forall cn v tl,
    lookup_row cn ((cn,v)::tl) = Some v.
Proof.
  intros cn v tl. simpl.
  destruct (String.string_dec cn cn) as [_|H]; [reflexivity|contradiction].
Qed.

Lemma lookup_row_singleton :
  forall cn v,
    lookup_row cn [(cn,v)] = Some v.
Proof.
  intros cn v. apply lookup_row_cons_eq.
Qed.




Lemma lookup_row_cons_neq :
  forall k cn v tl,
    k <> cn ->
    lookup_row cn ((k,v)::tl) = lookup_row cn tl.
Proof.
  intros k cn v tl Hneq. simpl.
  destruct (String.string_dec k cn) as [Heq|]; [contradiction|reflexivity].
Qed.



Lemma eval_proj_valsF_cons :
  forall evalRex r p tl vs,
    eval_proj_valsF evalRex r (p :: tl) = Some vs ->
    exists v vs',
      evalRex r (snd p) = Some v /\
      eval_proj_valsF evalRex r tl = Some vs' /\
      vs = v :: vs'.
Proof.
  intros evalRex r p tl vs H.
  simpl in H.
  destruct p as [cn e]; simpl in *.
  destruct (evalRex r e) as [v|] eqn:He; try discriminate.
  destruct (eval_proj_valsF evalRex r tl) as [vs'|] eqn:Htl; try discriminate.
  inversion H; subst vs.
  exists v, vs'. repeat split; auto.
Qed.



Lemma project_rowF_single :
  forall evalRex cn e r r',
    project_rowF evalRex [(cn,e)] r = Some r' ->
    exists v,
      evalRex r e = Some v /\ r' = [(cn, v)].
Proof.
  intros evalRex cn e r r' H.
  unfold project_rowF in H.
  simpl in H. (* map fst [(cn,e)] = [cn] *)
  destruct (nodup_stringb [cn]) eqn:Hnd; try discriminate.
  simpl in H. (* eval_proj_valsF on one element *)
  destruct (evalRex r e) as [v|] eqn:He; try discriminate.
  destruct (eval_proj_valsF evalRex r []) as [vs|] eqn:Hvs; try discriminate.
  (* eval_proj_valsF ... [] = Some [] *)
  simpl in Hvs. inversion Hvs; subst vs.
  inversion H; subst r'.
  exists v. split; auto.
Qed.



Lemma project_rowF_single_lookup :
  forall evalRex cn e r r' v,
    project_rowF evalRex [(cn,e)] r = Some r' ->
    evalRex r e = Some v ->
    lookup_row cn r' = Some v.
Proof.
  intros evalRex cn e r r' v Hpr He.
  pose proof (project_rowF_single evalRex cn e r r' Hpr) as [v' [He' ->]].
  rewrite He in He'. inversion He'. subst v'. apply lookup_row_singleton.
Qed.



Lemma class_row_has_oid :
  forall M SS SC DB C ts rows r,
    EncSchemaW M SC ->
    EncDBW M SS SC DB ->
    In C (CLASS M) ->
    lookup_table (sc_data SC) C = Some ts ->
    db_data SC DB C = Some rows ->
    In r rows ->
    exists o os,
      sigma_CLASS M SS C = Some os /\
      In o os /\
      lookup_row oid_col r = Some (Ira_Object C o).




Lemma EncSchemaW_class_table_exists :
  forall (M : object_model) (SC : Schema) (c : class_name),
    EncSchemaW M SC ->
    In c (CLASS M) ->
    exists ts,
      lookup_table (sc_data SC) c = Some ts /\
      ClassTable_ok M c ts.
Proof.
  intros M SC c HEncSc Hin.
  unfold EncSchemaW, EncSchema in HEncSc.
  destruct HEncSc as [Hcls _].
  specialize (Hcls c Hin).
  exact Hcls.
Qed.



Lemma class_row_oid_from_EncDBW :
  forall (M : object_model) (SS : system_state M)
         (SC : Schema) (DB : DBInstance SC)
         (c : class_name) (rows : list RowData) (r : RowData),
    EncSchemaW M SC ->
    EncDBW M SS SC DB ->
    In c (CLASS M) ->
    db_data SC DB c = Some rows ->
    In r rows ->
    exists o os,
      sigma_CLASS M SS c = Some os /\
      In o os /\
      lookup_row oid_col r = Some (Ira_Object c o).
Proof.
  intros M SS SC DB c rows r HEncSc HEncDB HinC Hdb Hinr.

  (* 1) 由 EncSchemaW 得到类表 ts 存在 *)
  unfold EncSchemaW, EncSchema in HEncSc.
  destruct HEncSc as [Hcls _].
  specialize (Hcls c HinC).
  destruct Hcls as [ts [Htab _HClassOk]].

  (* 2) 用 EncDBW 的类表一致性拿到 ClassTableInst_ok *)
  unfold EncDBW, EncDB in HEncDB.
  destruct HEncDB as [Hdb_cls _Hdb_assoc].
  specialize (Hdb_cls c ts rows HinC Htab Hdb).
  unfold ClassTableInst_ok in Hdb_cls.
  destruct Hdb_cls as [_Hcover Hback].

  (* 3) 用“反向性”把任意行 r ∈ rows 回溯到某个对象 o ∈ sigma_CLASS *)
  specialize (Hback r Hinr).
  destruct Hback as [o [os [Hsig [Hino Hrowok]]]].

  (* 4) 从 ClassObjectRow_ok 里取出 oid 列性质 *)
  unfold ClassObjectRow_ok in Hrowok.
  destruct Hrowok as [Hoid _].

  exists o, os.
  repeat split; auto.
Qed.







Lemma project_rowsF_in :
  forall evalRex ps rows out r',
    project_rowsF evalRex ps rows = Some out ->
    In r' out ->
    exists r, In r rows /\ project_rowF evalRex ps r = Some r'.
Proof.
  intros evalRex ps rows.
  induction rows as [|r rs IH]; intros out r' Hproj Hin.
  - (* rows = [] *)
    simpl in Hproj. inversion Hproj; subst out.
    simpl in Hin. contradiction.
  - (* rows = r :: rs *)
    simpl in Hproj.
    destruct (project_rowF evalRex ps r) as [r1|] eqn:Hr; try discriminate.
    destruct (project_rowsF evalRex ps rs) as [out_rs|] eqn:Hrs; try discriminate.
    inversion Hproj; subst out.
    simpl in Hin. destruct Hin as [Hin_hd | Hin_tl].
    + (* r' = r1 *)
      subst r'. exists r. split; [left; reflexivity| exact Hr].
    + (* r' ∈ out_rs *)
      specialize (IH out_rs r' eq_refl Hin_tl) as [r0 [Hin0 Hrow0]].
      exists r0.
      split.
      -- right; exact Hin0.
      -- exact Hrow0.
Qed.



(* 把 I_h 编码成数据库里的 I_ra；非对象值不支持时返回 None *)
Definition enc_Ih (ih : I_h) : option I_ra :=
  match ih with
  | Ih_Object C o => Some (Ira_Object C o)
  | _ => None
  end.








Lemma lookup_row_some_in :
  forall cn r v,
    lookup_row cn r = Some v ->
    In (cn, v) r.
Proof.
  intros cn r; induction r as [| [k w] tl IH]; intros v H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (String.string_dec k cn) as [Heq|Hneq].
    + inversion H; subst. left. now subst.
    + right. apply IH. exact H.
Qed.


Lemma in_combine_nth_error :
  forall (ks : list string) (vs : list I_ra) k v,
    In (k, v) (combine ks vs) ->
    exists i,
      nth_error ks i = Some k /\
      nth_error vs i = Some v.
Proof.
  intros ks vs; revert vs.
  induction ks as [|k0 ks IH]; intros vs k v Hin.
  - simpl in Hin. contradiction.
  - destruct vs as [|v0 vs]; simpl in Hin.
    + contradiction.
    + simpl in Hin.
      destruct Hin as [Hin | Hin].
      * inversion Hin; subst.
        exists 0. simpl. auto.
      * specialize (IH vs k v Hin) as [i [Hk Hv]].
        exists (S i). simpl. auto.
Qed.




Lemma eval_proj_valsF_nth :
  forall evalRex r0 ps vs i cn e,
    eval_proj_valsF evalRex r0 ps = Some vs ->
    nth_error ps i = Some (cn, e) ->
    exists v,
      nth_error vs i = Some v /\
      evalRex r0 e = Some v.
Proof.
  intros evalRex r0 ps.
  induction ps as [| [cn0 e0] ps IH]; intros vs i cn e Heval Hnth.
  -  rewrite nth_error_nil in Hnth. discriminate Hnth.
  - simpl in Heval.
    destruct (evalRex r0 e0) as [v0|] eqn:He0; try discriminate.
    destruct (eval_proj_valsF evalRex r0 ps) as [vs'|] eqn:Htl; try discriminate.
    inversion Heval; subst vs; clear Heval.
    destruct i as [|i'].
    + simpl in Hnth. inversion Hnth; subst cn e.
      exists v0. simpl. auto.
    + simpl in Hnth.
    (* 用 IH 在 vs' 里找出对应 v *)
    destruct (IH vs' i' cn e eq_refl Hnth) as [v [Hvs Heval]].
    exists v.
    split.
    -- (* nth_error (v0::vs') (S i') = Some v *)
      simpl. exact Hvs.
    -- exact Heval.

Qed.






Lemma nth_error_map_fst_exists :
  forall (ps : list (string * rex)) i k,
    nth_error (map fst ps) i = Some k ->
    exists e, nth_error ps i = Some (k, e).
Proof.
  intros ps; induction ps as [| [k0 e0] tl IH]; intros i k H.
  - rewrite nth_error_nil in H. discriminate H.
  - destruct i as [|i'].
    + simpl in H. inversion H; subst k.
      exists e0. simpl. reflexivity.
    + simpl in H.
      specialize (IH i' k H) as [e He].
      exists e. simpl. exact He.
Qed.




Lemma existsb_eqb_true_iff :
  forall x xs,
    existsb (String.eqb x) xs = true <-> In x xs.
Proof.
  intros x xs; induction xs as [|y ys IH]; simpl.
  - split; intro H; try discriminate; contradiction.
  - rewrite Bool.orb_true_iff.
    rewrite IH.
    split.
    + intro H. destruct H as [H|H].
      * left. apply String.eqb_eq in H. rewrite H. reflexivity.
      * right. exact H.
    + intro H. destruct H as [H|H].
      * left. apply String.eqb_eq. rewrite H. reflexivity.
      * right. exact H.
Qed.

Lemma nodup_stringb_sound :
  forall xs, nodup_stringb xs = true -> NoDup xs.
Proof.
  intro xs; induction xs as [|x tl IH]; simpl; intro H.
  - constructor.
  - apply Bool.andb_true_iff in H.
    destruct H as [Hnot Htl].
    apply Bool.negb_true_iff in Hnot.
    (* existsb ... tl = false *)
    assert (~ In x tl).
    { intro Hin.
      apply existsb_eqb_true_iff in Hin.
      (* Hin : existsb (String.eqb x) tl = true *)
      rewrite Hin in Hnot. discriminate.
    }
    constructor.
    + exact H.
    + apply IH. exact Htl.
Qed.




Lemma in_pair_same_fst_unique :
  forall (ps : list (string * rex)) k e1 e2,
    NoDup (map fst ps) ->
    In (k, e1) ps ->
    In (k, e2) ps ->
    e1 = e2.
Proof.
  intros ps; induction ps as [| [k0 e0] tl IH]; intros k e1 e2 Hnd Hin1 Hin2.
  - contradiction.
  - simpl in Hnd.
    inversion Hnd as [|k0' tl' Hnotin Hnd_tl]; subst k0' tl'.
    simpl in Hin1, Hin2.
    destruct Hin1 as [H1|H1]; destruct Hin2 as [H2|H2].
    + inversion H1; inversion H2; subst. reflexivity.
    + inversion H1; subst.
      (* (k,e0) in head, (k,e2) in tail *)
      exfalso.
      apply Hnotin. apply (in_map fst) in H2. exact H2.
    + inversion H2; subst.
      (* (k,e1) in tail, (k,e0) in head *)
      exfalso.
      apply Hnotin. apply (in_map fst) in H1. exact H1.
    + (* both in tail *)
      eapply IH; eauto.
Qed.





Lemma project_rowF_pullback_idcol :
  forall evalRex ps r0 r v,
    (forall row cn v, evalRex row (RCol cn) = Some v -> lookup_row cn row = Some v) ->
    In (val_col, RCol val_col) ps ->
    project_rowF evalRex ps r0 = Some r ->
    lookup_row val_col r = Some v ->
    lookup_row val_col r0 = Some v.
Proof.
  intros evalRex ps r0 r v Hcol Hid Hproj Hlook.
  unfold project_rowF in Hproj.
  destruct (nodup_stringb (map fst ps)) eqn:Hnodup; try discriminate.
  destruct (eval_proj_valsF evalRex r0 ps) as [vs|] eqn:Heval; try discriminate.
  inversion Hproj; subst r; clear Hproj.

  (* lookup_row -> In pair *)
  apply lookup_row_some_in in Hlook.
  (* In (val_col,v) (combine (map fst ps) vs) -> nth index *)
  eapply in_combine_nth_error in Hlook.
  destruct Hlook as [i [Hk Hv]].

  destruct (nth_error_map_fst_exists ps i val_col Hk) as [e Hnth_ps].

  destruct (eval_proj_valsF_nth evalRex r0 ps vs i val_col e Heval Hnth_ps)
    as [v' [Hv' He_e]].
  rewrite Hv in Hv'. inversion Hv'; subst v'; clear Hv'.

  pose proof (nodup_stringb_sound (map fst ps) Hnodup) as HNoDup.

  assert (In (val_col, e) ps) as Hin_ve.
  { eapply nth_error_In. exact Hnth_ps. }


  pose proof (in_pair_same_fst_unique ps val_col (RCol val_col) e HNoDup Hid Hin_ve) as Heq.
  subst e.

  apply (Hcol r0 val_col v).
  exact He_e.

Qed.





Lemma project_rowF_pullback_idcol_gen :
  forall evalRex ps r0 r cn v,
    (forall row cn v, evalRex row (RCol cn) = Some v -> lookup_row cn row = Some v) ->
    In (cn, RCol cn) ps ->
    project_rowF evalRex ps r0 = Some r ->
    lookup_row cn r = Some v ->
    lookup_row cn r0 = Some v.
Proof.
  intros evalRex ps r0 r cn v Hcol Hid Hproj Hlook.
  unfold project_rowF in Hproj.
  destruct (nodup_stringb (map fst ps)) eqn:Hnodup; try discriminate.
  destruct (eval_proj_valsF evalRex r0 ps) as [vs|] eqn:Heval; try discriminate.
  inversion Hproj; subst r; clear Hproj.

  apply lookup_row_some_in in Hlook.
  eapply in_combine_nth_error in Hlook.
  destruct Hlook as [i [Hk Hv]].

  destruct (nth_error_map_fst_exists ps i cn Hk) as [e Hnth_ps].

  destruct (eval_proj_valsF_nth evalRex r0 ps vs i cn e Heval Hnth_ps)
    as [v' [Hv' He_e]].
  rewrite Hv in Hv'. inversion Hv'; subst v'; clear Hv'.

  pose proof (nodup_stringb_sound (map fst ps) Hnodup) as HNoDup.

  assert (In (cn, e) ps) as Hin_ve.
  { eapply nth_error_In. exact Hnth_ps. }

  pose proof (in_pair_same_fst_unique ps cn (RCol cn) e HNoDup Hid Hin_ve) as Heq.
  subst e.

  apply (Hcol r0 cn v).
  exact He_e.
Qed.















Lemma project_rowsF_in_inv
  (evalRex : RowData -> rex -> option I_ra)
  (ps : list (ColName * rex))
  (rows0 rows1 : list RowData)
  (r : RowData)
  :
  project_rowsF evalRex ps rows0 = Some rows1 ->
  In r rows1 ->
  exists r0,
    In r0 rows0 /\
    project_rowF evalRex ps r0 = Some r.
Proof.
  revert rows1 r.
  induction rows0 as [|r0 rs IH]; intros rows1 r Hproj Hin.
  - simpl in Hproj. inversion Hproj; subst rows1. contradiction.
  - simpl in Hproj.
    destruct (project_rowF evalRex ps r0) as [r0'|] eqn:Hpr; try discriminate.
    destruct (project_rowsF evalRex ps rs) as [out|] eqn:Hrs; try discriminate.
    inversion Hproj; subst rows1; clear Hproj.
    simpl in Hin.
    destruct Hin as [Hr_eq | Hin_out].
    + subst r.
      exists r0. split.
      * left. reflexivity.
      * exact Hpr.
    + (* 这里用“first”兼容两种 IH 形状 *)
      destruct (IH out r) as [r00 [Hin00 Hpr00]].
      * first [ exact Hrs | exact eq_refl ].
      * exact Hin_out.
      * exists r00.
        split.
        -- right. exact Hin00.
        -- exact Hpr00.
Qed.









Lemma evalRexF_col :
  forall SC (DB : DBInstance SC) row cn v,
    evalRexF SC DB row (RCol cn) = Some v ->
    lookup_row cn row = Some v.
Proof.
  intros SC DB row cn v H.
  simpl in H. (* 这里会把 evalRexF 的 RCol 分支化简成 lookup_row *)
  exact H.
Qed.






Lemma BRIDGE_rows2_to_ih_true
  (M : object_model) (SS : system_state M)
  (SC : Schema) (DB : DBInstance SC)
  (E : env) (C : class_name) (expr : tm)
  (xs_all : list I_h)
  (rows0 rows1 : list RowData)
  (r : RowData)
  (evalRex : RowData -> rex -> option I_ra)
  (ps1 : list (ColName * rex))
  :
  EncSchemaW M SC ->
  EncDBW M SS SC DB ->

  (exists oids,
      sigma_CLASS M SS C = Some oids /\
      xs_all = map (fun oid => Ih_Object C oid) oids) ->

  project_rowsF evalRex ps1 rows0 = Some rows1 ->
  In r rows1 ->
  evalRex r (RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true)))
    = Some (Ira_Bool true) ->

  (* A: 走法A，把列读取语义当作假设引入 *)
  (forall (row : RowData) (cn : ColName) (v : I_ra),
      evalRex row (RCol cn) = Some v ->
      lookup_row cn row = Some v) ->

  (* B: 行上 val_col=true -> 对应 OCL not expr 求值 true *)
  (forall (ih : I_h) (r0 : RowData),
      lookup_row "self" r0 = enc_Ih ih ->
      lookup_row val_col r0 = Some (Ira_Bool true) ->
      exists vb : val_b,
        cevalF M SS (update E "self" (mk_var_b ih []))
              (CUnop (U_Bool UNot) expr) = Some vb /\
        val_val vb = Ie_Single (Ih_Basic (Ib_Bool true))) ->

  (* C: rows0 的每行 self 对应 xs_all 中某个 ih *)
  (forall r0,
      In r0 rows0 ->
      exists ih,
        In ih xs_all /\
        lookup_row "self" r0 = enc_Ih ih) ->

  (* 需要 val_col 是 identity 投影这一事实，供 pullback 用 *)
  In (val_col, RCol val_col) ps1 ->

  (* 以及你已经有的 “cond=true -> lookup_row val_col = true” 桥 *)
  (forall r0 : RowData,
      evalRex r0 (RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true)))
        = Some (Ira_Bool true) ->
      lookup_row val_col r0 = Some (Ira_Bool true)) ->

  exists ih vb,
    In ih xs_all /\
    cevalF M SS (update E "self" (mk_var_b ih []))
          (CUnop (U_Bool UNot) expr) = Some vb /\
    val_val vb = Ie_Single (Ih_Basic (Ib_Bool true)).
Proof.
  intros HEncSc HEncDB Hxs Hallproj Hin Hcond
         Hcol Hexpreval_ok Hrows0_self Hid_ps1 Hcond_lookup_true.

  (* 1) 从 rows1 中的 r 反推出 rows0 中的 r0，使得 project_rowF ... r0 = Some r *)
  destruct (project_rowsF_in_inv evalRex ps1 rows0 rows1 r Hallproj Hin)
    as [r0 [Hin0 Hr0]].

  (* 2) 由 rows0_self 得到 ih ∈ xs_all 且 self 列编码 ih *)
  destruct (Hrows0_self r0 Hin0) as [ih [Hih_in Hself]].

  (* 3) 从 cond=true 得到投影后行 r 上 val_col=true *)
  pose proof (Hcond_lookup_true r Hcond) as Hval_true_r.

  (* 4) 用 pullback：把 r 上 val_col=true 拉回到 r0 上 *)
  assert (lookup_row val_col r0 = Some (Ira_Bool true)) as Hval_true_r0.
  {
    eapply project_rowF_pullback_idcol; eauto.
    (* 这里用到：
       - Hcol        : evalRex col -> lookup_row
       - Hid_ps1     : In (val_col, RCol val_col) ps1
       - Hr0         : project_rowF ... r0 = Some r
       - Hval_true_r : lookup_row val_col r = Some true
    *)
  }

  (* 5) 套 Hexpreval_ok 得到 vb *)
  destruct (Hexpreval_ok ih r0 Hself Hval_true_r0) as [vb [Hce Hvv]].

  exists ih, vb.
  repeat split; assumption.
Qed.





Lemma cond_eq_true_lookup_valcol :
  forall SC (DB : DBInstance SC) (r : RowData),
    evalRexF SC DB r
      (RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true)))
      = Some (Ira_Bool true) ->
    lookup_row val_col r = Some (Ira_Bool true).
Proof.
  intros SC DB r H.
  simpl in H.  (* 展开 evalRexF 的 RBinop *)
  (* 现在 H 是：
     match lookup_row val_col r, Some (Ira_Bool true) with
     | Some v1, Some v2 => binop_sem_ra (B_Comp BEq) v1 v2
     | _, _ => None
     end = Some (Ira_Bool true)
  *)
  destruct (lookup_row val_col r) as [v1|] eqn:Hlk; try discriminate.
  (* 化简 binop_sem_ra / comp_binop_sem_ra / lift_bool_Ie_ra *)
  simpl in H.
  (* binop_sem_ra -> comp_binop_sem_ra *)
  unfold binop_sem_ra in H; simpl in H.
  unfold comp_binop_sem_ra in H; simpl in H.
  unfold lift_bool_Ie_ra in H; simpl in H.
  (* comp_eq_sem_ra v1 (Ira_Bool true) 必须是 Some true *)
  unfold comp_eq_sem_ra in H.
  destruct v1; try discriminate.
  (* H : Some (Ira_Bool (Bool.eqb b true)) = Some (Ira_Bool true) *)
  destruct b; simpl in H; inversion H; reflexivity.
Qed.






Lemma bridge_rows1_true_from_lookup
  (M : object_model) (SS : system_state M)
  (SC : Schema) (DB : DBInstance SC)
  (E : env) (C : class_name) (expr : tm)
  (xs_all : list I_h) (rows1 : list RowData)
  :
  (* A) rows1 中每行 r 的 self 能对应到 xs_all 里的某个 ih *)
  (forall r,
      In r rows1 ->
      exists ih,
        In ih xs_all /\
        lookup_row "self" r = enc_Ih ih) ->

  (* B) 表达式层正确性：self=ih 且 val_col=true -> not expr 在 ih 上求值 true *)
  (forall ih r,
      lookup_row "self" r = enc_Ih ih ->
      lookup_row val_col r = Some (Ira_Bool true) ->
      exists vb,
        cevalF M SS (update E "self" (mk_var_b ih []))
              (CUnop (U_Bool UNot) expr) = Some vb /\
        val_val vb = Ie_Single (Ih_Basic (Ib_Bool true))) ->

  forall r,
    In r rows1 ->
    lookup_row val_col r = Some (Ira_Bool true) ->
    exists ih vb,
      In ih xs_all /\
      cevalF M SS (update E "self" (mk_var_b ih []))
            (CUnop (U_Bool UNot) expr) = Some vb /\
      val_val vb = Ie_Single (Ih_Basic (Ib_Bool true)).
Proof.
  intros Hrow1_self Hexpreval_ok r Hin1 Hval_true_r.
  destruct (Hrow1_self r Hin1) as [ih [Hih_in Hself_r]].
  destruct (Hexpreval_ok ih r Hself_r Hval_true_r) as [vb [Hce Hvv]].
  exists ih, vb. repeat split; assumption.
Qed.



(* 你的 cond *)
Definition cond_true : rex :=
  RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true)).

(* 选择 evalRex *)
Definition evalRex0 (SC : Schema) (DB : DBInstance SC) : RowData -> rex -> option I_ra :=
  fun r e => evalRexF SC DB r e.

(* A: RCol 分支就是 lookup_row，所以立刻能证 *)
Lemma evalRex0_col :
  forall SC (DB : DBInstance SC) (row : RowData) (cn : ColName) (v : I_ra),
    evalRex0 SC DB row (RCol cn) = Some v ->
    lookup_row cn row = Some v.
Proof. intros; cbn in H; exact H. Qed.



Lemma cond_true_lookup_valcol :
  forall SC (DB : DBInstance SC) (r : RowData),
    evalRexF SC DB r cond_true = Some (Ira_Bool true) ->
    lookup_row val_col r = Some (Ira_Bool true).
Proof.
  intros SC DB r H.
  unfold cond_true in H.
  cbn in H.
  (* evalRexF ... (RCol val_col) = lookup_row val_col r *)
  destruct (lookup_row val_col r) as [v|] eqn:Hlk; try discriminate.
  cbn in H.
  (* 右边 RLit true *)
  (* 现在是 binop_sem_ra (B_Comp BEq) v (Ira_Bool true) = Some (Ira_Bool true) *)
  unfold binop_sem_ra in H; cbn in H.
  unfold comp_binop_sem_ra in H; cbn in H.
  (* comp_eq_sem_ra v (Ira_Bool true) *)
  destruct v; try discriminate.
  (* v = Ira_Bool b *)
  cbn in H.
  (* lift_bool_Ie_ra (Some (Bool.eqb b true)) = Some (Ira_Bool true) *)
  unfold lift_bool_Ie_ra in H; cbn in H.
  inversion H; subst.
  destruct b; reflexivity.
Qed.






Lemma bridge_from_rows2
  (M : object_model) (SS : system_state M)
  (SC : Schema) (DB : DBInstance SC)
  (E : env) (C : class_name) (expr : tm)
  (xs_all : list I_h)
  (rows0 rows1 rows2 : list RowData)
  (ps1 : list (ColName * rex))
  :
  EncSchemaW M SC ->
  EncDBW M SS SC DB ->
  (exists oids,
      sigma_CLASS M SS C = Some oids /\
      xs_all = map (fun oid => Ih_Object C oid) oids) ->

  (* project: rows0 -> rows1 *)
  project_rowsF (evalRex0 SC DB) ps1 rows0 = Some rows1 ->

  (* select: rows1 -> rows2 *)
  select_rowsF (evalRex0 SC DB) cond_true rows1 = Some rows2 ->

  (* B: 行上 val_col=true -> not expr=true (你已有的表达式正确性实例) *)
  (forall (ih : I_h) (r0 : RowData),
      lookup_row "self" r0 = enc_Ih ih ->
      lookup_row val_col r0 = Some (Ira_Bool true) ->
      exists vb : val_b,
        cevalF M SS (update E "self" (mk_var_b ih []))
              (CUnop (U_Bool UNot) expr) = Some vb /\
        val_val vb = Ie_Single (Ih_Basic (Ib_Bool true))) ->

  (* C: rows0 每行 self 对应 xs_all 某 ih *)
  (forall r0,
      In r0 rows0 ->
      exists ih,
        In ih xs_all /\
        lookup_row "self" r0 = enc_Ih ih) ->

  (* identity 投影：val_col := RCol val_col 在 ps1 里 *)
  In (val_col, RCol val_col) ps1 ->

  forall r2,
    In r2 rows2 ->
    evalRexF SC DB r2 cond_true = Some (Ira_Bool true) ->
    exists ih vb,
      In ih xs_all /\
      cevalF M SS (update E "self" (mk_var_b ih []))
            (CUnop (U_Bool UNot) expr) = Some vb /\
      val_val vb = Ie_Single (Ih_Basic (Ib_Bool true)).
Proof.
  intros HEncSc HEncDB Hxs Hproj Hsel Hexpreval_ok Hrows0_self Hid r2 Hin2 Hcond2.

  (* 1) rows2 -> rows1，并得到 cond=true（你已经有 select_rowsF_in_true） *)
  pose proof (select_rowsF_in_true (evalRex0 SC DB) cond_true rows1 rows2 r2 Hsel Hin2)
    as [Hin1 _Hcond2'].

  (* 2) 用你给的 BRIDGE_rows2_to_ih_true（注意它的 r ∈ rows1） *)
  eapply (BRIDGE_rows2_to_ih_true
            M SS SC DB E C expr xs_all rows0 rows1 r2 (evalRex0 SC DB) ps1);
    eauto.
   (* In r2 rows1 *)
      intros r0 Hc.
  unfold evalRex0 in Hc.
  eapply cond_true_lookup_valcol; eauto.

Qed.




Lemma in_stringb_true_iff :
  forall (x : string) (xs : list string),
    in_stringb x xs = true <-> In x xs.
Proof.
  intros x xs.
  unfold in_stringb.
  induction xs as [|y ys IH]; simpl.
  - split; intro H; try discriminate; contradiction.
  - rewrite Bool.orb_true_iff.
    rewrite IH.
    split.
    + intro H. destruct H as [H|H].
      * left. apply String.eqb_eq in H. rewrite H. reflexivity.
      * right. exact H.
    + intro H. destruct H as [H|H].
      * left. apply String.eqb_eq. rewrite H. reflexivity.
      * right. exact H.
Qed.


Lemma in_proj_cols :
  forall vl x,
    In x vl ->
    In (x, RCol x) (proj_cols vl).
Proof.
  intros vl x Hin.
  unfold proj_cols.
  apply in_map_iff.
  exists x. split; auto.
Qed.




Lemma lookup_row_in_NoDup :
  forall cn v r,
    NoDup (map fst r) ->
    In (cn,v) r ->
    lookup_row cn r = Some v.
Proof.
  intros cn v r Hnd Hin.
  induction r as [|[k w] tl IH]; simpl in *.
  - contradiction.
  - inversion Hnd as [|k' tl' Hnotin Hnd']; subst.
    simpl in Hin. destruct Hin as [Hin|Hin].
    + inversion Hin; subst.
      destruct (String.string_dec cn cn); [reflexivity|contradiction].
    + destruct (String.string_dec k cn) as [Heq|Hneq].
      * subst cn.
        exfalso. apply Hnotin.
        apply in_map with (f:=fst) in Hin. exact Hin.
      * apply IH; auto.
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
Theorem inv_semantic_preservation
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
  cevalF M SS E (inv_tm C expr) = Some vb ->
  (* 2) 翻译成功，且翻译出来是 Rel ra *)
  translate M empty (inv_tm C expr) = Some (Rel ra, vl, te, dim) ->
  (* 3) RA 求值 *)
  evalRelF SC DB ra = Some rows ->
  (* 4) 结果对应：空则空；非空则元素 multiset 相同 *)
  ocl_ra_inv_res_ok C (val_val vb) rows.
Proof.
  intros HEncSc HEncDB Hceval Htr HevalRA.
  (* 1) 展开 inv_tm，确保最外层能看到 CSelect *)
  unfold inv_tm in *.

  (* 2) 对 OCL 的求值推导做反演：应该命中 E_CSelect *)
  inversion Hceval; subst.
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
    inversion Htr. subst.
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

    cbn.  (* 简化 val_val *)

    cbn in H0.
    destruct (evalRelF SC DB rel0) as [rows0|] eqn:Hrel0; try discriminate.
    destruct (project_rowsF (fun r e => evalRexF SC DB r e)
            (proj_cols vl0 ++ [mkProj val_col (RUnop (U_Bool UNot) (RCol val_col))]) rows0)
      as [rows1|] eqn:Hproj1; try discriminate.
    destruct (select_rowsF (fun r e => evalRexF SC DB r e)
            (RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true))) rows1)
      as [rows2|] eqn:Hsel; try discriminate.
    cbn in H0.
    rename H0 into Hproj2.


    unfold ocl_ra_inv_res_ok.
    (* 展开 Hceval / Hproj2 里的 match 链 *)
    cbn in Hproj2.

    destruct (sigma_CLASS M SS C) as [oids|] eqn:Hclass; try discriminate.
    cbn in Hproj2.

    (* 这里 vb1 是 CAllInstances 的结果 *)
    destruct
      (Some
        {| val_val := Ie_Bag (Th_Object C) (map (fun oid => Ih_Object C oid) oids);
            val_deps := [] |})
      as [vb1|] eqn:Hv1; try discriminate.
    cbn in Hproj2.

    (* 继续拆 val_val vb1 *)
    (* 这一步通常会直接进 Ie_Bag 分支，所以只需 cbn *)
    cbn in Hproj2.

    (* 拆 go xs = Some out *)
    (* 你 Hproj2 里 go 的参数名叫 xs；cbn 后应该能看到 (go (map ... oids)) *)
    remember (map (fun oid => Ih_Object C oid) oids) as xs_all.
    unfold option_bind in Hproj2.
    destruct (selectF M SS (fun E' t' => cevalF M SS E' t')
                E "self" (CUnop (U_Bool UNot) expr) (Th_Object C) [] xs_all)
      as [out|] eqn:HselF; try discriminate.
    (* 现在 Hproj2 变成：Some {|... out ...|} = Some vb *)
    inversion Hproj2; subst vb.

                
    exists out.
    split.
    -- reflexivity.   (* 因为 val_val vb 已经化成 Ie_Bag ... out *)

    

    -- destruct out as [|ih out_tl].
      --- left. split; [reflexivity|].
        destruct (in_stringb "self" vl0) eqn:Hins; simpl in H1; try discriminate.
        inversion H1; subst ra vl te dim; clear H1.


(* 你可能已经有：project_rowsF_on_nil *)
(* Lemma project_rowsF_on_nil :
     forall evalRex ps out,
       project_rowsF evalRex ps [] = Some out -> out = []. *)

assert (Hrows2_nil : rows2 = []).
{
  (* 用反证：假设 rows2 有元素，就会产生 ih 使 not expr=true，与 Hall_false 冲突 *)
  destruct rows2 as [|r2 rs2] eqn:Hr2.
  - reflexivity.
  - exfalso.
    (* r2 ∈ rows2 *)
    assert (Hin2 : In r2 (r2 :: rs2)) by (left; reflexivity).
    (* 由 select_rowsF_in 得到 r2 ∈ rows1 且 cond_true=true *)
    pose proof (select_rowsF_in (fun r e => evalRexF SC DB r e) 
                 (RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true)))
                 rows1 (r2::rs2) r2 Hsel Hin2) as [Hin1 Hcond2].

    (* 现在从 Hcond2 推 lookup_row val_col r2 = true *)
    assert (Hval_true_r2 : lookup_row val_col r2 = Some (Ira_Bool true)).
    { eapply cond_true_lookup_valcol; eauto. }

    (* 关键：你需要一个 rows1 行 -> xs_all ih 的桥；如果你已用 bridge_from_rows2 建好了 Hbridge_rows2_true，就直接用它 *)
    (* 这里我写成：用你已证明的 bridge_from_rows2 得到 ih not expr=true *)
    (* 你需要 ps1 = (proj_cols vl0 ++ [mkProj val_col (RUnop ...)])，且包含 (val_col,RCol val_col) 才能用 pullback。
       你如果还没把 identity 投影加进 ps1，那么这里不能直接用 BRIDGE_rows2_to_ih_true。
       但你此处实际上是在 rows2 上 r2 自己已有 val_col=true，不需要 pullback，可以直接用“self->ih”桥。
       所以给一个更弱桥：Hrows1_self : forall r, In r rows1 -> exists ih, In ih xs_all /\ lookup_row "self" r = enc_Ih ih
       如果你没有它，就需要从你的翻译不变式/EncDBW 推出来。 *)




      assert (Hrows0_self :
        forall r0 : RowData,
          In r0 rows0 ->
          exists ih : I_h,
            In ih xs_all /\
            lookup_row "self" r0 = enc_Ih ih).
      {
        (* 这里填你真正的来源：
          - 如果 rel0 就是由 RATable C / RAProject 出来的类表行
          - 或者你已有 lemma 能从 EncDBW + Hrel0 推出每行都有 oid/self
          - 或者你把它作为主 lemma 的参数/假设传进来（走法A）
        *)
        (* 暂时先 admit，保证你后面 proof 能走通 *)
        admit.
      }






       
    (* 假设你已经有 Hrows1_self : ... （通常由 project_rowsF_in_inv + Hrows0_self + self identity 投影） *)
    (* 这里我用 admit 占位，你替换成你已有的桥 lemma *)
    assert (Hrows1_self :
      forall r,
        In r rows1 ->
        exists ih, In ih xs_all /\ lookup_row "self" r = enc_Ih ih).
    {
      
    assert (forall r,
          In r rows1 ->
          exists ih,
            In ih xs_all /\
            lookup_row "self" r = enc_Ih ih) as Hrows1_self.
    {
      intros r Hin_r1.

      (* 由 Hins 得到 In "self" vl0 *)
      assert ( Hin_self_vl0 : In "self" vl0 ).
      { apply (proj1 (in_stringb_true_iff "self" vl0)).
        exact Hins.
      }

      (* 得到 ("self", RCol "self") ∈ ps1 *)
      assert (Hid_self :
        In ("self", RCol "self")
          (proj_cols vl0 ++ [mkProj val_col (RUnop (U_Bool UNot) (RCol val_col))])).
      {
        apply in_or_app. left.
        apply in_proj_cols. exact Hin_self_vl0.
      }

      (* rows1 来自 project_rowsF ... rows0 *)
      (* 用 project_rowsF_in_inv 回溯到 r0 ∈ rows0 *)
      destruct (project_rowsF_in_inv
                  (fun (r : RowData) (e : rex) => evalRexF SC DB r e)
                  (proj_cols vl0 ++ [mkProj val_col (RUnop (U_Bool UNot) (RCol val_col))])
                  rows0 rows1 r
                  Hproj1 Hin_r1)
        as [r0 [Hin0 Hr0]].

      (* 用 Hrows0_self : r0 ∈ rows0 -> exists ih ... self 在 r0 *)
      destruct (Hrows0_self r0 Hin0) as [ih [Hih_in Hself0]].

      (* 把 self 列从 r0 拉回到 r *)
      (* 注意：这里 evalRex = evalRexF，所以列读取公理 Hcol 直接用 evalRexF_col *)
      assert (lookup_row "self" r = enc_Ih ih) as Hself_r.
      {
        (* pullback 的方向是：lookup_row cn r = v -> lookup_row cn r0 = v
          但我们现在已知 r0 的 self，想推出 r 的 self。
          所以我们改用 pullback 在“等价”方向：先证明 r 的 self = v，再 pullback？
          更简单：用 project_rowF 的构造式把 r = combine ... vs，直接用 lookup_row 的 combine 方向。
          但你已有的是 pullback（r -> r0）。要走 r0 -> r，需要一个 forward lemma。
          最省事：用 uniqueness + Hid_self，把投影项就是 RCol "self"，然后用 eval_proj_valsF_nth 得到 r 上 self 的值就是 evalRexF r0 (RCol "self") = lookup_row "self" r0。
        *)
        (* 我给你一个可直接用的做法：把 Hr0 unfold，取出 combine 结构，再用 in_combine_nth_error 反推。 *)
        unfold project_rowF in Hr0.
        destruct (nodup_stringb
                    (map fst (proj_cols vl0 ++ [mkProj val_col (RUnop (U_Bool UNot) (RCol val_col))])))
          eqn:Hnd; try discriminate.
        destruct (eval_proj_valsF (fun r e => evalRexF SC DB r e) r0
                    (proj_cols vl0 ++ [mkProj val_col (RUnop (U_Bool UNot) (RCol val_col))]))
          as [vs|] eqn:Heval; try discriminate.
        inversion Hr0; subst r; clear Hr0.

        (* 关键：由于 ("self", RCol "self") ∈ ps 且 NoDup(map fst ps)，self 列在 combine 里对应的值就是 evalRexF r0 (RCol "self") *)
        (* 这里我建议你单独做一个 lemma：project_rowF_forward_col
          但为了不让你再卡，我给“直接用 nth”版本：*)

        (* 由 Hid_self 找到它在 ps 中的 index i *)
        (* 用标准库 lemma In_nth_error: *)
        destruct (In_nth_error _ _ Hid_self) as [i Hi].
        (* Hi : nth_error ps i = Some ("self", RCol "self") *)

        (* 从 Heval + Hi 得到 nth_error vs i = Some v 且 evalRexF r0 (RCol "self") = Some v *)
        destruct (eval_proj_valsF_nth
                    (fun r e => evalRexF SC DB r e)
                    r0
                    (proj_cols vl0 ++ [mkProj val_col (RUnop (U_Bool UNot) (RCol val_col))])
                    vs i "self" (RCol "self") Heval Hi)
          as [v [Hv Hcolv]].

        (* Hcolv : evalRexF ... r0 (RCol "self") = Some v, 所以 v = lookup_row "self" r0 *)
        assert (Some v = enc_Ih ih).
        {
          unfold evalRexF in Hcolv. simpl in Hcolv.
          (* Hcolv : lookup_row "self" r0 = Some v *)
          (* 但 Hself0 : lookup_row "self" r0 = enc_Ih ih *)
          (* enc_Ih ih : option I_ra，所以这里类型要一致：
            你 Hself0 里是 option I_ra，而 lookup_row 返回 option I_ra。
            所以 Hself0 应该形如 lookup_row "self" r0 = Some (Ira_Object ...)。
            你当前 enc_Ih ih 也是 option，所以通常 Hself0 的 RHS 是 enc_Ih ih，本身就是 option。
            那么上面 v 是 I_ra，需要把 Hself0 改写成 Some v = enc_Ih ih 的形状。
          *)
          (* 最稳的：把 Hcolv 和 Hself0 同时 rewrite： *)
          rewrite Hcolv in Hself0.
          (* Hself0 : Some v = enc_Ih ih *)
          inversion Hself0. reflexivity.
        }
        subst.

        (* 最后证明 lookup_row "self" (combine (map fst ps) vs) = enc_Ih ih *)
        (* combine 里 self 的值在第 i 个位置是 enc_Ih ih *)
        (* 用一个你已有的 lemma：project_rowF_single_lookup 类似方式；
          这里我直接用 lookup_row + in_combine_nth_error 的逆方向：
          先证明 In ("self", enc_Ih ih) (combine ...), 再用 lookup_row ... = Some ...。
        *)
        (* 由于 nth_error(map fst ps) i = Some "self" 且 nth_error vs i = Some (enc_Ih ih) *)
        assert (In ("self", enc_Ih ih) (combine (map fst
          (proj_cols vl0 ++ [mkProj val_col (RUnop (U_Bool UNot) (RCol val_col))])) vs)).
        {
          (* 用 nth_error 版本的 In: *)
          apply (nth_error_In_combine _ _ i); auto.
        }
        (* 然后用 lookup_row_some_in 的逆（你可能没有），这里更简单：直接计算 lookup_row 在 combine 上的值会比较麻烦。
          所以我建议你：定义并用 lemma lookup_row_combine_nth_error:
              nth_error ks i = Some k ->
              nth_error vs i = Some v ->
              NoDup ks ->
              lookup_row k (combine ks vs) = Some v
          你现在已经写了很多 list lemma，这个一写就通用。
        *)
        admit.
      }

      exists ih. split; [exact Hih_in | exact Hself_r].


        
    }


    assert (Hexpreval_ok :
      forall ih r0,
        lookup_row "self" r0 = enc_Ih ih ->
        lookup_row val_col r0 = Some (Ira_Bool true) ->
        exists vb,
          cevalF M SS (update E "self" (mk_var_b ih []))
            (CUnop (U_Bool UNot) expr) = Some vb /\
          val_val vb = Ie_Single (Ih_Basic (Ib_Bool true))).
    {
      (* 这里用你之前的 bridge lemma 或语义一致性 lemma *)
      (* 如果你还没证明，就 admit，先推进主定理 *)
      admit.
    }

(* 先把 Hall_false 建出来：selectF 返回 [] => 所有元素都 eval 为 false *)
pose proof
  (selectF_nil_all_false
     M SS
     (fun (E' : env) (t' : tm) => cevalF M SS E' t')
     E "self" (CUnop (U_Bool UNot) expr)
     (Th_Object C) [] xs_all
     HselF)
  as Hall_false.


    (* 用你刚写的 bridge_rows1_true_from_lookup *)
    pose proof (bridge_rows1_true_from_lookup
      M SS SC DB E C expr xs_all rows1
      Hrows1_self Hexpreval_ok
      r2 Hin1 Hval_true_r2) as [ih [vb [Hih_in [Hce_true Hvv_true]]]].

    (* 由 Hall_false 知道每个 ih 上 not expr 都是 false，矛盾 *)
    specialize (Hall_false ih Hih_in) as [vbF [HceF HvvF]].
    rewrite Hce_true in HceF. inversion HceF; subst vbF.
    rewrite Hvv_true in HvvF. discriminate.
}

(* 最后用 H2 展开 evalRelF：Project(Select(Project(rel0))) *)
subst rows2.
(* 1) 先把 H2 化简，把 [...] 展开成你 Hproj1 里的那一项 *)
cbn in H2.

(* 2) 把 evalRelF rel0 替换成 rows0 *)
rewrite Hrel0 in H2.
(* 3) 现在内层 project_rowsF 那一坨应该能和 Hproj1 匹配了 *)
rewrite Hproj1 in H2.

(* 4) 你已经有 Hsel : select_rowsF ... rows1 = Some [] *)
rewrite Hsel in H2.
cbn in H2.

inversion H2; subst.
reflexivity.














        
--- right. split; [discriminate|].
  (* 构造 oids1 oids2 并证明 bag_equiv_oids *)
  admit.
