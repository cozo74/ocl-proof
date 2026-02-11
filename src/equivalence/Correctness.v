From Stdlib Require Import String ZArith Reals List.
Import ListNotations.
Open Scope string_scope.

From OCL.equivalence Require Import Models Utils.
From OCL.equivalence Require Import OCLSyntax OCLSemantic.
From OCL.equivalence Require Import RASyntax RASemantic.
From OCL.equivalence Require Import Translation. 
From OCL.equivalence Require Import CorrectnessLemmas. 

From Stdlib Require Import Permutation.
From Stdlib Require Import Program.Equality.




(* 语法糖：class.allInstances->select(self | expr) *)
Definition inv_tm (C : class_name) (expr : tm) : tm :=
  CSelect (CAllInstances C) "self" (CUnop (U_Bool UNot) expr).





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
  3) OCL 语义求值成功，产生 OCL 结果 vb
         cevalR ... (inv_tm C expr) vb
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
      OCL 不变量检查 = SQL / 关系代数查询
  在语义层面完全等价。
  换句话说：
      编译器没有改变语义。
  这是一个标准的：
    semantic preservation theorem编译正确性定理
*)
Theorem inv_semantic_preservation
  (M  : object_model)
  (SS : system_state M)
  (SC : Schema)
  (DB : DBInstance SC)
  (C  : class_name)
  (expr : tm)
  (E : env)
  (xs : list I_h)
  (ra : rel)
  (vl : list var_name)
  (te : T_e)
  (dim : rel)
  (rows : list RowData)
  :
  EncSchemaW M SC ->
  EncDBW M SS SC DB ->
  (* 1) OCL 求值：class.allInstances->select(self | not expr) 产生 vb *)
  cevalF M SS E (inv_tm C expr) =  Some (Ie_Bag (Th_Object C) xs) ->
  (* 2) 翻译成功，且翻译出来是 Rel ra *)
  translate M empty (inv_tm C expr) = Some (Rel ra, vl, te, dim) ->
  (* 3) RA 求值 *)
  evalRelF SC DB ra = Some rows ->
  (* 4) 结果对应：空则空；非空则元素 multiset 相同 *)
  (xs = [] <-> rows = []).
Proof.
  intros HEncSc HEncDB HcevalF Htranslate HevalRelF.
  (* 1) 展开 inv_tm，确保最外层能看到 CSelect *)
  unfold inv_tm in *.


  (* =====================  处理OCL求值  ===================== *)
  (* 2) 对 OCL 的求值推导做反演：应该命中 E_CSelect *)
  inversion HcevalF; subst.


  (* 1) 拆 H0 的外层 option_bind *)
  destruct (sigma_CLASS M SS C) as [oids|] eqn:Hoids; try discriminate.
  simpl in H0.

  (* 从 H0 抽出真正的 selectF = Some xs： *)
  unfold option_bind in H0.
  destruct (selectF M SS (fun E' t' => cevalF M SS E' t')
          E "self" (CUnop (U_Bool UNot) expr) (Th_Object C)
          (map (fun oid => Ih_Object C oid) oids)) eqn:HselF;
    try discriminate.
  inversion H0; subst.
  (* 得到 HselF : selectF ... = Some xs *)





  (* =====================  处理 translation  ===================== *)

  (* 3) 对翻译结果做结构化化简：translate 的 CSelect 分支 *)
  simpl in Htranslate.

  (* 确保类C在Object Model中存在 *)
  destruct (lookup_class M C) eqn:Hlc; try discriminate.
  
  simpl in Htranslate.


  (* 1) 把内层 translate 记住 *)
  remember
    (translate M
      (update empty "self"
        (RAProject [mkProj val_col (RCol oid_col)] (RATable C),
          [], Th_Object C)) expr)
    as tr_self eqn:Htr_self.

  (* 2) 对 tr_self 分类 *)
  destruct tr_self as [[[[rex_or_rel vl0] te0] dim0] | ] eqn:Hcase; try discriminate.
  (* 1) 先分 rex_or_rel *)
  destruct rex_or_rel as [e1 | rel0].

  - (* Rex 分支：最终必须是 Some (Rel ...) -> 不可能 *)
    destruct vl0 as [|v vl0']; simpl in Htranslate; try discriminate.

    (* 先拆 te0 / dim0，看是否能产生 Some (Rex ...) *)
    destruct dim0; simpl in Htranslate; try discriminate.
    destruct te0 as [th0 | th0]; simpl in Htranslate; try discriminate.
    destruct th0 as [tb0 | c0]; simpl in Htranslate; try discriminate.
    destruct tb0; simpl in Htranslate; try discriminate.


  - (* Rel 分支 *)
    (* 先把 dim0 化掉 *)
    destruct dim0; simpl in Htranslate; try discriminate.

    (* te0 必须是 Te_Single (Th_Basic Tb_Bool) *)
    destruct te0 as [th0 | th0]; simpl in Htranslate; try discriminate.
    destruct th0 as [tb0 | c0]; simpl in Htranslate; try discriminate.
    destruct tb0; simpl in Htranslate; try discriminate.

    (* 外层 match 命中，需要 in_stringb "self" vl0 = true *)
    destruct (in_stringb "self" vl0) eqn:Hself; try discriminate.

    (* 现在 Htranslate 形如 Some = Some *)
    inversion Htranslate.
    (* subst. *)

    rewrite <- H1 in HevalRelF.
    (* 可选：rewrite <- H2 in *; rewrite <- H3 in *; rewrite <- H4 in *; *)

    simpl in HevalRelF.
    destruct (evalRelF SC DB rel0) as [rows0|] eqn:Hrel0; try discriminate.
    destruct (project_rowsF (fun r e => evalRexF SC DB r e)
            (proj_cols vl0 ++ [mkProj val_col (RUnop (U_Bool UNot) (RCol val_col))]) rows0)
      as [rows1|] eqn:Hproj1; try discriminate.
    destruct (select_rowsF (fun r e => evalRexF SC DB r e)
            (RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true))) rows1)
      as [rows2|] eqn:Hsel; try discriminate.
    (* 现在 HevalRelF 化成 project_rowsF ... rows2 = Some rows *)


  (* =====================  处理目标goal: ocl_ra_inv_res_ok  ===================== *)

    split.
    -- (* xs = [] -> rows = [] *)
      



    - (* rows = [] -> xs = [] *)
