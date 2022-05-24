(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "jacobisMethodX4ProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "a44" then (((1)/(1000), (10)/(1)):real#real)
  else if x = Short "b4" then (((1)/(1000), (10)/(1)):real#real)
  else if x = Short "x1" then (((0)/(1), (10)/(1)):real#real)
  else if x = Short "x2" then (((0)/(1), (10)/(1)):real#real)
  else if x = Short "x3" then (((0)/(1), (10)/(1)):real#real)
  else if x = Short "x4" then (((0)/(1), (10)/(1)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "jacobisMethodX4")
    (Fun "a44"(Fun "b4"(Fun "x1"(Fun "x2"(Fun "x3"(Fun "x4"
      (FpOptimise Opt
        (Let (SOME "x_n4")
        (App (FP_bop FP_Sub)
          [
            (App (FP_bop FP_Sub)
            [
              (App (FP_bop FP_Add)
              [
                (App (FP_bop FP_Div)
                [
                  Var (Short  "b4");
                  Var (Short  "a44")
                ]);
                (App (FP_bop FP_Mul)
                [
                  (App (FP_bop FP_Div)
                  [
                    (App FpFromWord [Lit (Word64 (4591870180066957722w:word64))]);
                    Var (Short  "a44")
                  ]);
                  Var (Short  "x1")
                ])
              ]);
              (App (FP_bop FP_Mul)
              [
                (App (FP_bop FP_Div)
                [
                  (App FpFromWord [Lit (Word64 (4596373779694328218w:word64))]);
                  Var (Short  "a44")
                ]);
                Var (Short  "x2")
              ])
            ]);
            (App (FP_bop FP_Mul)
            [
              (App (FP_bop FP_Div)
              [
                (App FpFromWord [Lit (Word64 (4599075939470750515w:word64))]);
                Var (Short  "a44")
              ]);
              Var (Short  "x3")
            ])
          ])
        (Var (Short  "x_n4"))))))))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()