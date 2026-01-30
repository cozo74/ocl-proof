From Stdlib Require Import String ZArith Reals List.
Import ListNotations.
Open Scope string_scope.

From OCL.equivalence Require Import Models OCLSyntax RASyntax RASemantic OCLTyping Utils. 











(* 取 schema 的最后一列 *)
Definition last_col (cols : list string) : option string :=
    match rev cols with
    | [] => None
    | c :: _ => Some c
    end.




Definition groupkey := list string.






(* === 小工具：投影 GK / GK_r，以及 GK 等值连接条件 === *)





  
Definition proj_cols (cs : list string)
: list RAProjItem :=
map
  (fun c =>
     {| proj_expr := RCol c
      ; proj_name := c |})
  cs.



Fixpoint proj_cols_r (CS : list string) : list RAProjItem :=
    match CS with
    | [] => []
    | c :: cs =>
        {| proj_expr := RCol c; proj_name := String.append c "_r" |}
          :: proj_cols_r cs
    end.
  


Fixpoint mk_cols_join_cond (CS : list string) : option rex :=
    match CS with
    | [] => None
    | c :: cs =>
        let e0 :=
          RBinop (B_Comp BEq)  (RCol c) (RCol (String.append c "_r")) in
        match mk_cols_join_cond cs with
        | None => Some e0
        | Some e => Some (RBinop (B_Bool BAnd) e0 e)
        end
    end.
  





Definition last_col_ty (cols : list Column) : option T_ra :=
  match rev cols with
  | [] => None
  | c :: _ => Some (col_ty c)
  end.


Definition rename_if_in
  (l1 l2 : list var_name) : list var_name :=
  map
    (fun x =>
       if existsb (String.eqb x) l1
       then x ++ "_r"
       else x)
    l2.




(* 求两个list var_name的交集（去重）, keep_left *)
Definition inter_var (l1 l2 : list var_name) : list var_name :=
  filter (fun x => existsb (String.eqb x) l2) l1.


(* 求两个list var_name的并集（去重）, keep_left *)
Fixpoint union_var (l1 l2 : list var_name) : list var_name :=
  match l2 with
  | [] => l1
  | x :: xs =>
      if existsb (String.eqb x) l1
      then union_var l1 xs
      else union_var (List.app l1 [x]) xs
  end.





Inductive rex_or_rel : Type :=
    | Rex : rex -> rex_or_rel
    | Rel : rel -> rex_or_rel.


Definition tran_env := partial_map (rel * list var_name * T_h).


Definition val_col := "_elem".
Definition val_col_r := "_elem_r".


Fixpoint translate (M : object_model) (E : tran_env) (t : tm) : option (rex_or_rel * list var_name * T_e) := 
    match t with

    
    (* ======================== Var 表达式 ======================== *)
    (* 
        转换规则:
        - 从tran_env中查找变量x的替换rel
        - 将x加入rel的依赖变量中，表示当前表达式的取值依赖变量x
        - 表达式的类型为原rel的类型
    *)
    | CVar x =>
        match E x with
        | Some (r, vl, th) => Some (Rel r, List.app vl [x], Te_Single th)
        | None => None
        end




    (* ======================== operation 表达式 ======================== *)

    (*  无参operation： 字面量构造器  *)
    (* 
        转换规则:
        - 根据basic type字面量的值，创建对应的Rex，表示一个标量
        - 一个标量不存在依赖变量，依赖变量列表为空
        - 类型为值的类型
    *)
    | CLit v => 
        match v with
          |  Ib_Bool b => Some (Rex (RLit (Ira_Bool b)), [], Te_Single (Th_Basic Tb_Bool))
          |  Ib_Int z => Some (Rex (RLit (Ira_Int z)), [], Te_Single (Th_Basic Tb_Int))
          |  Ib_Real r => Some (Rex (RLit (Ira_Real r)), [], Te_Single (Th_Basic Tb_Real))
          |  Ib_String s => Some (Rex (RLit (Ira_String s)), [], Te_Single (Th_Basic Tb_String))
        end




    (*  basic type 有参operation： 一元操作  *)
    (* 
        转换规则:
        - 若t为rex
            - 转换为Rex的一元操作
            - 一个标量不存在依赖变量，依赖变量列表为空
            - 类型由OCLTyping中unop_type函数计算得到
        - 若t为rel
            - 转换为Rel上的Project操作
                - 保留所有列
                - 将val_col列根据unop变换为新列
            - 依赖变量列表与源rel一致
            - 类型由OCLTyping中unop_type函数计算得到
    *)
    | CUnop op t =>
        match translate M E t with
        (* rex *)
        | Some (Rex e1, [], te) =>
            match unop_type op te with 
            | Some te' => 
                Some (Rex (RUnop op e1), [], te')
            | _ => None
            end
        (* rel *)
        | Some (Rel rel, vl, te) =>
            match unop_type op te with 
            | Some te' => 
                let vcols := proj_cols vl in
                let nv := mkProj val_col (RUnop op (RCol val_col)) in
                Some (
                    Rel (RAProject (List.app vcols [nv]) rel),
                    vl,
                    te'
                )
            | _ => None
            end
        | _ => None
        end



    (*  basic type 有参operation： 二元操作 (和object type eq)  *)
    (* 
        转换规则:
        - 若t1为rex，t2为rex
        - 若t1为rex，t2为rel
        - 若t1为rel，t2为rex
        - 若t1为rel，t2为rel
    *)

    | CBinop op t1 t2 =>
        match translate M E t1, translate M E t2 with
        (* rex 与 rex
            转换规则:
            - 若t1为rex，t2为rex
                - 转换为Rex的二元操作
                - 一个标量不存在依赖变量，依赖变量列表为空
                - 类型由OCLTyping中binop_type函数计算得到
        *)
        | Some (Rex e1, [], te1), Some (Rex e2, [], te2) =>
            match binop_type op te1 te2 with 
            | Some te' =>
                Some (Rex (RBinop op e1 e2), [], te')
            | _ => None
            end
        (* rex 与 rel 
            转换规则:
            - 若t1为rex，t2为rel
            - 若t1为rel，t2为rex
                - 转换为Rel上的Project操作
                    - 保留所有列
                    - 将val_col列根据binop变换为新列
                - 依赖变量列表与源rel一致
                - 类型由OCLTyping中binop_type函数计算得到
        *)
        | Some (Rex e1, [], te1), Some (Rel rel2, vl2, te2) =>
            match binop_type op te1 te2 with 
            | Some te' =>
                let vcols := proj_cols vl2 in
                let nv := mkProj val_col (RBinop op e1 (RCol val_col)) in
                Some (
                    Rel (RAProject (List.app vcols [nv]) rel2),
                    vl2,
                    te'
                )
            | _ => None
            end

        (* rel 与 rex *)
        | Some (Rel rel1, vl1, te1), Some (Rex e2, [], te2) =>
            match binop_type op te1 te2 with 
            | Some te' =>
                let vcols := proj_cols vl1 in
                let nv := mkProj val_col (RBinop op (RCol val_col) e2) in
                Some (
                    Rel (RAProject (List.app vcols [nv]) rel1),
                    vl1,
                    te'
                )
            | _ => None
            end


        (* rel 与 rel
            转换规则:
            - 若t1为rel，t2为rel
                - 转换为两个rel的rename+(join+project/cartesian+project)
                - 准换为两个rel的join+project操作
                    - join条件为：所有相同依赖变量相等
                    - 对join结果进行投影，投影出两个依赖变量列表的并集（去重），
                        将val_col列根据binop变换为新列
                - 依赖变量列表为两个依赖变量列表的并集（去重）
                - 类型由OCLTyping中binop_type函数计算得到
        *)
        (* join时将右表相同列重命名为带_r后缀 *)
        | Some (Rel rel1, vl1, te1), Some (Rel rel2, vl2, te2) =>
            let projcols := List.app (proj_cols (rename_if_in vl1 vl2)) [mkProj val_col_r (RCol val_col)] in
            let intercols := inter_var vl1 vl2 in
            let unioncols := union_var vl1 vl2 in 
            let procols := proj_cols unioncols in
            let nv := mkProj val_col (RBinop op (RCol val_col) (RCol val_col_r)) in
            match binop_type op te1 te2 with 
            | Some te' =>
                match intercols with 
                (* 两个rel不存在相同依赖变量 *)
                | [] => 
                    let cart_res := RACartesian rel1 (RAProject projcols rel2) in
                    Some (
                            Rel (RAProject (List.app procols [nv]) cart_res),
                            unioncols,
                            te'
                    )

                (* 两个rel存在相同依赖变量 *)
                | x :: xs => 
                    match mk_cols_join_cond intercols with 
                    | Some jcond =>
                        let join_res := RAJoin jcond rel1 (RAProject projcols rel2) in
                        
                        Some (
                            Rel (RAProject (List.app procols [nv]) join_res),
                            unioncols,
                            te'
                        )

                    | _ => None
                    end
                end
            | _ => None
            end
        | _, _ => None
        end




    (*  object type 有参operation： allInstances, 对象属性/角色  *)
    (* 
        转换规则:
        - 转换为 表扫描+project oid列为val_col
    *)
    | CAllInstances class =>
        match lookup_class M class with
        | Some table =>
            Some (
                Rel ( RAProject [(mkProj val_col (RCol oid_col))] (RATable class)),
                [],
                Te_Single (Th_Object class)
                )
        | None => None
        end




    (* 
        转换规则:
        - 转换为 join+project
            - tm 成功转换为一个表示cn类型对象的 rel
            - 从 object model中成功查找到该类存在attr字段，表示对象表objTable存在、字段存在
            -将tm转换的结果rel和 对象对应的表objTable进行连接操作，
                连接条件为rel的最后一列（val_col）和对象表objTable的oid_col相等，
            - 最后投影出rel中除了val_col的所有列，以及将objTable中的attr列投影为val_col列，
                类型为attr的类型
    *)
    | CAttr tm attr =>
        match translate M E tm with
        | Some (Rel rel, vl, Te_Single (Th_Object cn) ) =>
            match lookup_attr_type M cn attr with
            | Some tb =>
                let jocnd := RBinop (B_Comp BEq)  (RCol val_col) (RCol oid_col) in
                let vcol := mkProj val_col (RCol attr) in
                let projcols := List.app (proj_cols vl) [vcol] in
                    Some (
                        Rel (RAProject projcols (RAJoin jocnd rel (RATable cn))),
                        vl,
                        Te_Single (Th_Basic tb)
                    )

            | _ => None
            end
        | _ => None
        end










    (* 
        转换规则:
        - 转换为 join+project
            - tm 成功转换为一个表示cn类型对象的 rel
            - 从 object model中成功查找到该类存在assoc关系和role字段，表示关系表assoTable存在、字段存在
            -将tm转换的结果rel和 关系表assoTable进行连接操作，
                连接条件为rel的最后一列（val_col）和关系表assoTable的role列相等，
            - 最后投影出rel中除了val_col的所有列，以及将assoTable中的role列投影为val_col列，
                类型为role对应的对象的类型
    *)
    | CRole tm role =>
        match translate M E tm with
        | Some (Rel rel, vl, Te_Single (Th_Object cn) ) =>
            match lookup_role_type M cn role,
                lookup_assoc_of_role M cn role,
                lookup_nav_multiplicity M cn role with
            | Some cn', Some asso, Some One =>
                let jocnd := RBinop (B_Comp BEq)  (RCol val_col) (RCol role) in
                let vcol := mkProj val_col (RCol role) in
                let projcols := List.app (proj_cols vl) [vcol] in
                    Some (
                        Rel (RAProject projcols (RAJoin jocnd rel (RATable asso))),
                        vl,
                        Te_Single (Th_Object cn')
                    )
            | _, _, _ => None
            end
        | _ => None
        end





    (* 
        转换规则:
        - 转换为 join+project
            - tm 成功转换为一个表示cn类型对象的 rel
            - 从 object model中成功查找到该类存在assoc关系和role字段，表示关系表assoTable存在、字段存在
            -将tm转换的结果rel和 关系表assoTable进行连接操作，
                连接条件为rel的最后一列（val_col）和关系表assoTable的role列相等，
            - 最后投影出rel中除了val_col的所有列，以及将assoTable中的role列投影为val_col列，
                类型为role对应的对象的集合的类型
    *)
    | CNRole tm nrole =>
        match translate M E tm with
        | Some (Rel rel, vl, Te_Single (Th_Object cn) ) =>
            match lookup_role_type M cn nrole,
                lookup_assoc_of_role M cn nrole,
                lookup_nav_multiplicity M cn nrole with
            | Some cn', Some asso, Some Many =>
                let jocnd := RBinop (B_Comp BEq)  (RCol val_col) (RCol nrole) in
                let vcol := mkProj val_col (RCol nrole) in
                let projcols := List.app (proj_cols vl) [vcol] in
                    Some (
                        Rel (RAProject projcols (RAJoin jocnd rel (RATable asso))),
                        vl,
                        Te_Bag (Th_Object cn')
                    )
            | _, _, _ => None
            end
        | _ => None
        end




    (*  Bag type 有参operation： 字面量构造器 *)
    (* 
        转换规则:
        - 转换为 一列多行的RABagLiteral
        - 依赖变量列表为空
        - 类型为值的集合的类型
    *)
    | CBagLiteral tb tl =>
        let tra := enc_Tb tb in
        let tl' := map enc_Ib tl in
        Some (
            Rel (RABagLiteral tra tl'),
            [],
            Te_Bag (Th_Basic tb)
        )







    (*  Bag type 有参operation： Bag 集合运算  *)
    (*  Bag union  *)
    (* 
        转换规则:
        - 若rel1，rel2都只有一列val_col列（即依赖变量列表为空）
        - 若rel1依赖变量列表不为空，rel2只有一列val_col列
        - 若rel1只有一列val_col列，rel2依赖变量列表不为空
        - 若rel1，rel2都依赖变量列表不为空
    *)
    | CUnion t1 t2 =>
        match translate M E t1, translate M E t2 with
        | Some (Rel rel1, vl1, te1), Some (Rel rel2, vl2, te2) =>
            match vl1, vl2 with 
            | [], [] => 
            (* 
                转换规则:
                - 若rel1，rel2都只有一列val_col列（即依赖变量列表为空）
                    - 转换为RAUnion操作
                    - 依赖变量列表为空
                    - 类型为te1 （ 若为有效的语句，te1=te2）
            *)
                Some (
                    Rel (RAUnion rel1 rel2),
                    [],
                    te1
                ) 
            | x :: xs, [] => 
            (* 
                转换规则:
                - 若rel1依赖变量列表不为空，rel2只有一列val_col列
                    - 转换为规则如下
                        - 投影出rel1除val_col外的所有列（即所有依赖变量列表列），并去重，作为rel1'
                        - 将rel1'与rel2进行笛卡尔积作为rel2''（将rel2中所有元素依次分配给rel1中的每个bag）
                        - 最后将rel1与rel2''进行RAUnion操作
                    - 依赖变量列表为t1的依赖变量列表
                    - 类型为te1 （ 若为有效的语句，te1=te2）
            *)
                let rel1' := RADistinct (RAProject (proj_cols vl1) rel1) in
                let rel2'' := RACartesian rel1' rel2 in
                Some (
                    Rel (RAUnion rel1 rel2''),
                    vl1,
                    te1
                )




            | [], x :: xs => 
            (* 
                转换规则:
                - 若rel1只有一列val_col列，rel2依赖变量列表不为空
                    - 转换为规则如下
                        - 投影出rel2除val_col外的所有列（即所有依赖变量列表列），并去重，作为rel2'
                        - 将rel1与rel2'进行笛卡尔积作为rel1''（将rel1中所有元素依次分配给rel2中的每个bag）
                        - 最后将rel1''与rel2进行RAUnion操作
                    - 依赖变量列表为t2的依赖变量列表
                    - 类型为te1 （ 若为有效的语句，te1=te2）
            *)
                let rel2' := RADistinct (RAProject (proj_cols vl2) rel2) in
                let rel1'' := RACartesian rel2' rel1 in
                Some (
                    Rel (RAUnion rel1'' rel2),
                    vl2,
                    te1
                )


            | x1 :: xs1, x2 :: xs2 => 
            (* 
                转换规则:
                - 若rel1，rel2都依赖变量列表不为空
                    - 转换为规则如下
                        - 投影出rel1,rel2除val_col外的所有列（即所有依赖变量列表列），并去重，作为rel1',rel2'
                        - 计算vl1与vl2交集
                            - 若交集为空，表示不存在相同依赖变量
                                - 将rel1与rel2'进行笛卡尔积作为rel1'', 将rel1'与rel2进行笛卡尔积作为rel2''
                            - 若交集不为空，表示存在相同依赖变量，连接条件为相同依赖变量相等
                                - 将相同列（相同依赖变量）重命名为带_r后缀
                                - 将rel1与rel2'进行连接作为rel1'', 将rel1'与rel2进行连接作为rel2''
                        - 最后使用project操作调整列顺寻，然后将rel1''与rel2''进行RAUnion操作
                    - 依赖变量列表为两个依赖变量列表的并集（去重）
                    - 类型为te1 （ 若为有效的语句，te1=te2）
            *)
                let rel1' := RADistinct (RAProject (proj_cols vl1) rel1) in
                let rel2' := RADistinct (RAProject (proj_cols vl2) rel2) in
                let intercols := inter_var vl1 vl2 in
                let unioncols := union_var vl1 vl2 in 
                match intercols with 
                (* 两个rel不存在相同依赖变量 *)
                | [] => 
                    (* 列顺序乱了 *)
                    let rel1'' := RACartesian rel1 rel2' in
                    let rel2'' := RACartesian rel1' rel2 in 
                    let projcols := List.app (proj_cols unioncols) [mkProj val_col_r (RCol val_col) ] in
                    Some (
                        (* 使用project调整列顺序 *)
                        Rel (RAUnion (RAProject projcols rel1'') (RAProject projcols rel2'')),
                        unioncols,
                        te1
                    )


                (* 两个rel存在相同依赖变量 *)
                | x :: xs => 
                    match mk_cols_join_cond intercols with
                    | Some jcond =>
                        let rel1' := RADistinct (RAProject (proj_cols vl1) rel1) in
                        let rel2' := RADistinct (RAProject (proj_cols vl2) rel2) in

                        (* 对相同列进行重命名 *)
                        let recols2 := rename_if_in vl1 vl2 in
                        let recols1 := rename_if_in vl2 vl1 in
                        let rel1'' := RAJoin jcond rel1 (RAProject (proj_cols recols2) rel2') in
                        let rel2'' := RAJoin jcond (RAProject (proj_cols recols1) rel1') rel2 in
                        (* 使用project调整输出顺序 *)
                        let outcols := proj_cols (List.app unioncols [val_col]) in
                        Some (
                            Rel (RAUnion (RAProject outcols rel1'') (RAProject outcols rel2'')),
                            unioncols,
                            te1
                        )

                    | _ => None
                    end
                end

            end

        | _, _ => None
        end






    (*  Bag difference  *)
    (* 
        转换规则:
        - 类似RAUnion，将RAUnion换为RADiff（！！差操作时可能会丢失空bag的组）
    *)
    | CDifference t1 t2  =>
        match translate M E t1, translate M E t2 with
        | Some (Rel rel1, vl1, te1), Some (Rel rel2, vl2, te2) =>
            match vl1, vl2 with 
            | [], [] => 
                Some (
                    Rel (RADiff rel1 rel2),
                    [],
                    te1
                ) 

            | x :: xs, [] => 
                let rel1' := RADistinct (RAProject (proj_cols vl1) rel1) in
                let rel2'' := RACartesian rel1' rel2 in
                Some (
                    Rel (RADiff rel1 rel2''),
                    vl1,
                    te1
                )


            | [], x :: xs => 
                let rel2' := RADistinct (RAProject (proj_cols vl2) rel2) in
                let rel1'' := RACartesian rel2' rel1 in
                Some (
                    Rel (RADiff rel1'' rel2),
                    vl2,
                    te1
                )


            | x1 :: xs1, x2 :: xs2 => 
                let rel1' := RADistinct (RAProject (proj_cols vl1) rel1) in
                let rel2' := RADistinct (RAProject (proj_cols vl2) rel2) in
                let intercols := inter_var vl1 vl2 in
                let unioncols := union_var vl1 vl2 in 
                match intercols with 
                (* 两个rel不存在相同依赖变量 *)
                | [] => 
                    (* 列顺序乱了 *)
                    let rel1'' := RACartesian rel1 rel2' in
                    let rel2'' := RACartesian rel1' rel2 in 
                    let projcols := List.app (proj_cols unioncols) [mkProj val_col_r (RCol val_col) ] in
                    Some (
                        (* 使用project调整列顺序 *)
                        Rel (RADiff (RAProject projcols rel1'') (RAProject projcols rel2'')),
                        unioncols,
                        te1
                    )


                (* 两个rel存在相同依赖变量 *)
                | x :: xs => 
                    match mk_cols_join_cond intercols with
                    | Some jcond =>
                        let rel1' := RADistinct (RAProject (proj_cols vl1) rel1) in
                        let rel2' := RADistinct (RAProject (proj_cols vl2) rel2) in

                        (* 对相同列进行重命名 *)
                        let recols2 := rename_if_in vl1 vl2 in
                        let recols1 := rename_if_in vl2 vl1 in
                        let rel1'' := RAJoin jcond rel1 (RAProject (proj_cols recols2) rel2') in
                        let rel2'' := RAJoin jcond (RAProject (proj_cols recols1) rel1') rel2 in
                        (* 使用project调整输出顺序 *)
                        let outcols := proj_cols (List.app unioncols [val_col]) in
                        Some (
                            Rel (RADiff (RAProject outcols rel1'') (RAProject outcols rel2'')),
                            unioncols,
                            te1
                        )

                    | _ => None
                    end
                end

            end

        | _, _ => None
        end






    (*  Bag type 有参operation： Bag 函数 。 可用select+size表示*)
    (* 
        转换规则:
        - 转换为按照依赖变量列表进行分组聚合，对val_col列进行聚合（相同依赖变量的行对应的val_col的值组成一个bag）
            - 若依赖变量列表为空，表示全局聚合，得到一个标量值？（TODO）
            - 若依赖变量列表不为空，表示分组聚合，转换为一个RAAggregate操作
        - 依赖变量列表与源rel一致
        - 类型由OCLTyping中aggop_type函数计算得到
    *)
    | CAggregate op tm =>
        match translate M E tm with
        | Some (Rel rel, vl, Te_Bag th ) =>
            match vl, aggop_type op th with 

            | [], Some te' =>
                None
                (* TODO *)

            |  x :: xs, Some te' =>
                Some (
                    Rel (RAAggregate vl [(val_col, op, val_col)] rel),
                    vl,
                    Te_Single te'
                )


            | _, _ => None
            end
        | _ => None
        end



    (* ======================== iterator 表达式 ======================== *)
 
    (*  Bag type 有参operation：Iterator。 可用select+size表示*)
    (* 
        转换规则:
        - 转换为对
            - 对t1求值得到rel1，将rel1作为变量var加入变量环境E作为E'
            - 在变量环境E'下对t2求值得到rel2，类型为Te_Single (Th_Basic Tb_Bool)
                rel2的var列为rel1中的val_col列，rel2中的val_col为得到的bool类型列
            - 选择出val_col为true的行，投影出vl1的所有列，以及将var列投影为val_col列（！！此时会丢失空bag的组，聚合操作可能会受影响，TODO）
        - 依赖变量列表与原rel一致
        - 表达式的类型为原rel的类型
    *)
    | CSelect t1 var t2 =>
        match translate M E t1 with
        | Some (Rel rel1, vl1, Te_Bag th ) =>
        (* 列形状为：(v1, v2, v3, val_col:th ), 行数为n *)
            let E' := update E var (rel1, vl1, th) in 
            match translate M E' t2 with
            | Some (Rel rel2, vl2, Te_Single (Th_Basic Tb_Bool) ) =>
            (* 列形状为：(v1, v2, v3, var:th, val_col:bool )。
                行数也应该为n，select操作(要求t2为带v的表达式)对bag中逐元素迭代得到一个bool值，
                即对rel1中每行进行操作得到一行，所以行数应该相同 *)
                let cond := RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true)) in
                let projcols := List.app (proj_cols vl1) [mkProj val_col (RCol var)] in
                Some (
                    Rel (RAProject projcols (RASelect cond rel2)),
                    vl1,
                    Te_Bag th
                )

    
            | _ => None
            end
    
        | _ => None
        end
    









    end.