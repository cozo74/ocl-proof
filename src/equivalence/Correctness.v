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
  inversion H0; subst; clear H0.
  (* 得到 HselF : selectF ... = Some xs *)





  (* =====================  处理 translation  ===================== *)

  (* 3) 对翻译结果做结构化化简：translate 的 CSelect 分支 *)
  simpl in Htranslate.

  (* 确保类C在Object Model中存在 *)
  destruct (lookup_class M C) eqn:Hlc; try discriminate.
  
  (* simpl in Htranslate. *)


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

  (* Rex 分支：最终必须是 Some (Rel ...) -> 不可能 *)
  destruct vl0 as [|v vl0']; simpl in Htranslate; try discriminate.

  (* 先拆 te0 / dim0，看是否能产生 Some (Rex ...) *)
  destruct dim0; simpl in Htranslate; try discriminate.
  destruct te0 as [th0 | th0]; simpl in Htranslate; try discriminate.
  destruct th0 as [tb0 | c0]; simpl in Htranslate; try discriminate.
  destruct tb0; simpl in Htranslate; try discriminate.


  (* Rel 分支 *)
  (* 先把 dim0 化掉 *)
  destruct dim0; simpl in Htranslate; try discriminate.

  (* te0 必须是 Te_Single (Th_Basic Tb_Bool) *)
  destruct te0 as [th0 | th0]; simpl in Htranslate; try discriminate.
  destruct th0 as [tb0 | c0]; simpl in Htranslate; try discriminate.
  destruct tb0; simpl in Htranslate; try discriminate.

  (* Set Printing All. *)

  (* 外层 match 命中，需要 in_stringb "self" vl0 = true *)
  (* destruct (list_string_eqb vl0 ["self":var_name]) eqn:Hvl0 in Htranslate; try discriminate. *)
  destruct (occurs_var "self" expr) eqn:Hvl0 in Htranslate; try discriminate.


  (* 现在 Htranslate 形如 Some = Some *)
  inversion Htranslate.
  (* subst. *)

  rewrite <- H0 in HevalRelF.
  rewrite <- H1 in *; rewrite <- H2 in *; rewrite <- H3 in *.
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


  (* =====================  处理目标 goal  ===================== *)

    split.
    - (* xs = [] -> rows = [] *)

      intro Hxs.
      destruct rows as [|r rs]; [reflexivity|].

      (* 此时矛盾点为：HevalRelF
      project_rowsF的结果rows应该为空，但HevalRelF条件中结果为r::rs，矛盾了，因此destruct rows2 *)
      
      destruct rows2 as [|r2 rows2'].
      + simpl in HevalRelF. discriminate. (* 此分支引起矛盾 *)
      + simpl in HevalRelF.
        destruct (project_rowF (fun r e => evalRexF SC DB r e)
                [mkProj val_col (RCol "self")] r2) as [r2'|] eqn:Hrow; try discriminate.
        destruct (project_rowsF (fun r e => evalRexF SC DB r e)
                [mkProj val_col (RCol "self")] rows2') as [rows2''|] eqn:Htail; try discriminate.
        inversion HevalRelF. 
        (* 得到 r2' = r, rows2'' = rs *)
        subst.

        (* 此时矛盾点为：Hsel
        select_rowsF的结果rows1应该为空，但 Hsel 条件中结果为r2::rows2'，矛盾了
        为什么rows1应该为空？因为对应的ocl表达式HselF结果为xs=[]
        HselF中，对于oids列表产生的所有Ih_Object C oid对象，将每个对象添加为环境变量self，执行表达式'CUnop (U_Bool UNot) expr'，选出表达式结果为true的结果集合为xs=[]，即所有oid都不满足表达式
        对应到RA侧，对应操作应该是：对RATable C投影出oid_col列对应了由oids生成的所有对象Ih_Object C oid集合，作为变量self的值（见Htr_self条件）；对ocl表达式expr的的翻译结果ra表达式为rel0，其应该包含了变量self列，和bool类型的val_col列，表示self所有可能取值时的bool结果
        由于所有self的可能取值expr都为true，取反后都为false，因此selectF的结果为xs=[]
        此时需要使用条件推出expr对应的ra表达式rel0的求值结果rows0的val_col列的值都为true，之后Hproj1中对rows0取反的结果rows1的所有val_col列的值都为false，之后select_rowsF的结果应该为[]，与Hsel条件中的结果r2::rows2'矛盾，因此最终结果可证
        因此此时应该想办法推出rel0的求值结果rows0的val_col列的值都为true，或者说找一个反例

        codex回复：
        你的方向里有一个可优化点：不需要证明 rows0 的 val_col 全都为 true。
        证明“全都 true”太强，而且没必要。当前分支里你已经有 Hsel : ... = Some (r2::rows2')，这已经给你一个反例见证，走“存在矛盾”即可。

        可走的最短链路：

        从 Hsel 拿到头行满足条件为真
        select_rowsF_in_true 给出：
        In r2 rows1
        evalRexF ... r2 (RBinop ... val_col = true) = Some (Ira_Bool true)
        即 r2.val_col = true（在 rows1 里）
        用 Hproj1 回溯 r2 到 rows0 的某行 r0
        project_rowsF_in 得到 In r0 rows0 且 project_rowF ... r0 = Some r2。
        再用 project_rowF_single_lookup（或你已有 lookup lemma）提取 rows1.val_col = not rows0.val_col。
        由第1+第2得到 rows0.val_col = false（某个对象上 expr=false）。
        用 class_row_oid_from_EncDBW 把这行 r0 映射回某个 oid ∈ oids。
        把第3翻回 OCL 侧，得到该 oid 上 not expr = true，与
        HselF : selectF ... (CUnop (U_Bool UNot) expr) ... oids = Some [] 冲突。
        这里需要你那个关键 lemma：selectF_nil_all_false（建议先补完并启用）。
        结论：
        当前分支不是去证“rows0 全真”，而是用 Hsel 提供的单个见证导出 HselF 的反例。这样闭环最稳。



        *)
        pose proof (select_rowsF_in_true
          (fun r e => evalRexF SC DB r e)
          (RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true)))
          rows1 (r2 :: rows2') r2
          Hsel (or_introl eq_refl)) as [Hin_rows1 Hcond_true].



        (* 0) 把 selectF 结果改写成 Some [] *)
        (* assert (HselF_nil :
          selectF M SS (fun E' t' => cevalF M SS E' t')
            E "self" (CUnop (U_Bool UNot) expr) (Th_Object C)
            (map (fun oid => Ih_Object C oid) oids) = Some []).
        { now rewrite Hxs in HselF. } *)

        (* 1) 从 rows1 回溯到 rows0 *)
        pose proof (project_rowsF_in
          (fun r e => evalRexF SC DB r e)
          (proj_cols vl0 ++ [mkProj val_col (RUnop (U_Bool UNot) (RCol val_col))])
          rows0 rows1 r2 Hproj1 Hin_rows1)
        as [r0 [Hin_rows0 Hproj_r0]].

        (* 2) 从 rows0 的行拿到对象 oid（EncDBW 桥接） *)
        assert (HinC : In C (CLASS M)).
        {
          unfold lookup_class in Hlc.
          destruct (existsb (String.eqb C) (CLASS M)) eqn:Hex; inversion Hlc; subst.
          now apply existsb_eqb_true_iff in Hex.
        }

        clear Htranslate.


        (* 这里需要先有一个证明：
        translate M E t1 = Some (Rel rel1, vl1, Te_Bag th, dim_rel ) ->
        unused_var var vl1 = true ->
        E' := update E var (rel1, vl1, th) ->
        translate M E' t2 = Some (Rel rel2, vl2, Te_Single (Th_Basic Tb_Bool), RAEmpty ) ->
        list_string_eqb vl2 (vl1 ++ [var]) = true ->
        evalRelF SC DB rel1 = Some rows1 ->
        evalRelF SC DB (RAProject (List.app (proj_cols vl1) [mkProj val_col (RCol var)]) rel2) = Some rows2 ->
        rows1 = rows2

        然后rows1为RATable C的求值结果，rows2为rel0（即带var表达式）的求值结果，可以对rows2投影得到RATable C的求值结果
        *)



        destruct (evalRelF SC DB
          (RAProject [mkProj val_col (RCol oid_col)] (RATable C)))
          as [rows0'|] eqn:Heval_row0';
        try (
          exfalso;
          symmetry in Htr_self;
          pose proof (
            translate_dep_none_propagates
              M SC DB
              empty "self" expr
              (RAProject [mkProj val_col (RCol oid_col)] (RATable C))
              rel0 [] vl0 C
              Hvl0 Heval_row0' Htr_self
          ) as Hnone_rel0;
          rewrite Hrel0 in Hnone_rel0;
          discriminate
        ).





        (* 1) 准备两个翻译前提 *)
        assert (Htr_bag :
          translate M empty (CAllInstances C) =
          Some (Rel (RAProject [mkProj val_col (RCol oid_col)] (RATable C)),
                [], Te_Bag (Th_Object C), RAEmpty)).
        { simpl. rewrite Hlc. reflexivity. }

        pose proof Htr_self as Htr_body.
        symmetry in Htr_body.

        (* 2) 先把 rel0 的 self 投影求值拿出来 *)
        destruct (evalRelF SC DB (RAProject [mkProj val_col (RCol "self")] rel0))
          as [rows_self|] eqn:Hselfproj.
        2:{ (* None 分支你可先留着，或后续用别的引理排除 *)
            admit. }

        (* 3) 实例化你的 admitted 引理 *)
        pose proof (
          cselect_body_row_shape_preservation_perm
            M SS SC DB
            empty
            (CAllInstances C) expr "self"
            (RAProject [mkProj val_col (RCol oid_col)] (RATable C))
            rel0
            RAEmpty
            []
            vl0
            rows0'
            rows_self
            C
            HEncDB
            (tran_env_wf_empty M SS SC DB)
            Htr_bag
            Htr_body
            Hvl0
            Heval_row0'
            Hselfproj
        ) as Hperm_rows.
        (* Hperm_rows : Permutation rows0' rows_self *)



        (* 反例r0从rows0传递到rows_self，再传递到rows0'*)

        (* 先把 Hselfproj 改写成 project_rowsF 形态 *)
        simpl in Hselfproj.
        rewrite Hrel0 in Hselfproj.
        
        pose proof (
          project_rowsF_in_fwd
            (fun r e => evalRexF SC DB r e)
            [mkProj val_col (RCol "self")]
            rows0 rows_self r0
            Hselfproj
            Hin_rows0
        ) as [r_self [Hin_rows_self Hproj_self_r0]].


        (* 反例r_self从rows_self再传递到rows0'*)
        assert (Hin_rows0' : In r_self rows0').
        { eapply Permutation_in.
          - exact (Permutation_sym Hperm_rows).
          - exact Hin_rows_self.
        }



        (* 展开良型性，得到rows'到rowsC，rowsC和oids的关系 *)

        simpl in Heval_row0'.
        destruct (db_data SC DB C) as [rowsC|] eqn:HdbC; simpl in Heval_row0'; try discriminate.

        unfold EncDBW, EncDB in HEncDB.
        destruct HEncDB as [Hdb_cls Hdb_assoc].



        (* 1) 先从 EncSchemaW 拿到类表 schema *)
        unfold EncSchemaW, EncSchema in HEncSc.
        destruct HEncSc as [Hcls _].
        specialize (Hcls C HinC).
        destruct Hcls as [ts [Htab _]].

        (* 2) 用 Hdb_cls + HdbC 得到 ClassTableInst_ok *)
        pose proof (Hdb_cls C ts rowsC HinC Htab HdbC) as HClassInst.
        unfold ClassTableInst_ok in HClassInst.
        destruct HClassInst as [Hcover [Hback Huniq]].

        (* 3) oids -> rowsC（覆盖性） *)
        assert (Hoids_to_rows :
          forall o, In o oids ->
            exists rC, In rC rowsC /\
              lookup_row oid_col rC = Some (Ira_Object C o)).
        {
          intros o Hino.
          specialize (Hcover o oids Hoids Hino) as [rC [Hinr Hrowok]].
          unfold ClassObjectRow_ok in Hrowok.
          destruct Hrowok as [Hoid _].
          exists rC; auto.
        }

        (* 4) rowsC -> oids（反向性） *)
        assert (Hrows_to_oids :
          forall rC, In rC rowsC ->
            exists o, In o oids /\
              lookup_row oid_col rC = Some (Ira_Object C o)).
        {
          intros rC Hinr.
          specialize (Hback rC Hinr) as [o [os [Hos [Hino Hrowok]]]].
          rewrite Hoids in Hos; inversion Hos; subst os.
          unfold ClassObjectRow_ok in Hrowok.
          destruct Hrowok as [Hoid _].
          exists o; auto.
        }





      (* 反例r0从rows0'传递到rowsC，再传递到oids*)

      (* 已有 Hin_rows0' : In r_self rows0' *)
      pose proof (
        project_rowsF_in
          (fun r e => evalRexF SC DB r e)
          [mkProj val_col (RCol oid_col)]
          rowsC rows0' r_self
          Heval_row0'
          Hin_rows0'
      ) as [rowC [Hin_rowC Hproj_rowC]].


      (* 从 rowsC -> oids *)
      pose proof (project_rowF_single
        (fun r e => evalRexF SC DB r e)
        val_col (RCol oid_col) rowC r_self Hproj_rowC) as [vo [Hoid_eval Hrself]].




        (* rowC -> 某个对象 o *)
        specialize (Hback rowC Hin_rowC) as [o [os [Hos [Hino Hrowok]]]].
        rewrite Hoids in Hos; inversion Hos; subst os.

        (* 取 oid 列 *)
        unfold ClassObjectRow_ok in Hrowok.
        destruct Hrowok as [Hoid_rowC _].





        (* 1) 由 rowC 的 oid 列，确定 vo = Ira_Object C o *)
        pose proof (evalRexF_col SC DB rowC oid_col vo Hoid_eval) as Hlookup_oid.
        rewrite Hlookup_oid in Hoid_rowC.
        inversion Hoid_rowC; subst vo.
        subst r_self.
        (* 现在 r_self = [(val_col, Ira_Object C o)] *)

        (* 2) 用 Hproj_self_r0 把 r0 的 self 列值取出来 *)
        pose proof (project_rowF_single
          (fun r e => evalRexF SC DB r e)
          val_col (RCol "self")
          r0
          [(val_col, Ira_Object C o)]
          Hproj_self_r0) as [v [Hself_eval Hout]].
        inversion Hout; subst v.
        (* 得到 Hself_eval :
          evalRexF SC DB r0 (RCol "self") = Some (Ira_Object C o) *)

        pose proof (evalRexF_col SC DB r0 "self" (Ira_Object C o) Hself_eval)
          as Hself_lookup.
        (* Hself_lookup : lookup_row "self" r0 = Some (Ira_Object C o) *)


        assert (Hin_obj :
          In (Ih_Object C o) (map (fun oid => Ih_Object C oid) oids)).
        { apply in_map. exact Hino. }

        pose proof (selectF_nil_no_true
          M SS (fun E' t' => cevalF M SS E' t')
          E "self" (CUnop (U_Bool UNot) expr) (Th_Object C)
          (map (fun oid => Ih_Object C oid) oids)
          HselF
          (Ih_Object C o)
          Hin_obj) as Hnot_true_o.

        assert (Hval_false : lookup_row val_col r0 = Some (Ira_Bool false)).
        { admit. }


        pose proof (
          ra_row_false_to_ceval_not_true_self_local_occurs
            M SS SC DB
            C expr E
            ts
            rel0 vl0
            rows0 r0 o
            Htab
            Hdb_cls
            HinC
            Htr_body
            Hvl0
            Hrel0
            Hin_rows0
            Hself_lookup
            Hval_false
        ) as Htrue_o.









      (* 与Hself中选出的结果为空矛盾，证明结束 *)
      exfalso.
      apply Hnot_true_o.
      exact Htrue_o.
      

    - (* rows = [] -> xs = [] *)
    admit. (* 证明思路：同上，反过来走一遍 *)
Admitted.
