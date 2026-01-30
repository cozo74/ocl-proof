




``` bash

coq_makefile -f _CoqProject -o Makefile
make
make clean
```



1. Models.v中定义了OCL、RA中的类型、值域，OCL中的Object Model，SystemState，RA中的Schema。DBInstance，以及Object Model和Schema的对应关系，SystemState和DBinstance的对应关系
2. OCLSyntax.v中定义了OCL的语法
3. OCLSemantic.v中定义了OCL的语义（大步求值，关系描述）
4. RASyntax.v中定义了RA的语法
5. RASemantic.v中定义了RA的语义（大步求值，关系描述）
6. Translation.v中定义了OCL到RA的转换函数


我现在如何定义语义一致性的定理？ 
我的理解是： 
forall ocl不变式， ocl不变式成功求值得到结果v -> 
ocl不变式成功转换为ra表达式 -> 
ra表达式成功求值得到结果v' -> 
v和v'满足值对应关系 

还是说应该更强一些： 
forall ocl不变式，ocl不变式成功求值得到结果v -> 
ocl不变式成功转换为ra表达式 /\ ra表达式成功求值得到结果v' /\ v和v'满足值对应关系
