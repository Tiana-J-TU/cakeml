(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "kepler1ProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "x1" then (((4)/(1), (159)/(25)):real#real)
  else if x = Short "x2" then (((4)/(1), (159)/(25)):real#real)
  else if x = Short "x3" then (((4)/(1), (159)/(25)):real#real)
  else if x = Short "x4" then (((4)/(1), (159)/(25)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "kepler1")
    (Fun "x1"(Fun "x2"(Fun "x3"(Fun "x4"
      (FpOptimise Opt
(App (FP_bop FP_Sub)
        [
          (App (FP_bop FP_Sub)
          [
            (App (FP_bop FP_Sub)
            [
              (App (FP_bop FP_Sub)
              [
                (App (FP_bop FP_Add)
                [
                  (App (FP_bop FP_Add)
                  [
                    (App (FP_bop FP_Mul)
                    [
                      (App (FP_bop FP_Mul)
                      [
                        Var (Short  "x1");
                        Var (Short  "x4")
                      ]);
                      (App (FP_bop FP_Sub)
                      [
                        (App (FP_bop FP_Add)
                        [
                          (App (FP_bop FP_Add)
                          [
                            (App (FP_uop FP_Neg)
                            [
                              Var (Short  "x1")
                            ]);
                            Var (Short  "x2")
                          ]);
                          Var (Short  "x3")
                        ]);
                        Var (Short  "x4")
                      ])
                    ]);
                    (App (FP_bop FP_Mul)
                    [
                      Var (Short  "x2");
                      (App (FP_bop FP_Add)
                      [
                        (App (FP_bop FP_Add)
                        [
                          (App (FP_bop FP_Sub)
                          [
                            Var (Short  "x1");
                            Var (Short  "x2")
                          ]);
                          Var (Short  "x3")
                        ]);
                        Var (Short  "x4")
                      ])
                    ])
                  ]);
                  (App (FP_bop FP_Mul)
                  [
                    Var (Short  "x3");
                    (App (FP_bop FP_Add)
                    [
                      (App (FP_bop FP_Sub)
                      [
                        (App (FP_bop FP_Add)
                        [
                          Var (Short  "x1");
                          Var (Short  "x2")
                        ]);
                        Var (Short  "x3")
                      ]);
                      Var (Short  "x4")
                    ])
                  ])
                ]);
                (App (FP_bop FP_Mul)
                [
                  (App (FP_bop FP_Mul)
                  [
                    Var (Short  "x2");
                    Var (Short  "x3")
                  ]);
                  Var (Short  "x4")
                ])
              ]);
              (App (FP_bop FP_Mul)
              [
                Var (Short  "x1");
                Var (Short  "x3")
              ])
            ]);
            (App (FP_bop FP_Mul)
            [
              Var (Short  "x1");
              Var (Short  "x2")
            ])
          ]);
          Var (Short  "x4")
        ]))))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()