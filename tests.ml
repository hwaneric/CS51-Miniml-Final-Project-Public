open Expr ;;
open Evaluation ;; 

open CS51Utils ;; 
open Absbook ;;

let free_vars_test () = 
    let empty = vars_of_list [] in 
    let set_x = vars_of_list ["x"] in 
    let set_x_y = vars_of_list ["x"; "y"] in
    unit_test (same_vars empty (free_vars (Num 5)))
               "free_vars int";

    unit_test (same_vars empty (free_vars (Bool true)))
               "free_vars bool"; 

    unit_test (same_vars empty (free_vars (Raise)))
               "free_vars raise"; 

    unit_test (same_vars empty (free_vars (Unassigned)))
               "free_vars unassigned"; 

    unit_test (same_vars set_x (free_vars (Var "x")))
               "free_vars variable x"; 

    unit_test (same_vars set_x (free_vars (Unop (Negate, Var "x"))))
               "free_vars -x";

    unit_test (same_vars set_x (free_vars (Binop (Plus, Var "x", Num 5))))
               "free_vars x + 5"; 
    unit_test (same_vars set_x (free_vars (Binop (Plus, Var "x", Var "x"))))
               "free_vars x + x";
    unit_test (same_vars set_x_y (free_vars (Binop (Plus, Var "x", Var "y"))))
               "free_vars x + y";
    unit_test (same_vars set_x_y (free_vars (Binop (Plus, Var "y", (Binop (Plus, Var "x", Var "x"))))))
               "free_vars y + x + x";

    unit_test (same_vars set_x_y (free_vars (Conditional ((Var "x"), (Var "x"), (Var "y")))))
               "free_vars if x then x else y";
    unit_test (same_vars set_x_y (free_vars (Conditional ((Binop (Equals, (Var "x"), (Num 5))), (Var "x"), (Var "y")))))
               "free_vars if x = 5 then x else y";
    
    unit_test (same_vars empty (free_vars (Fun ("x", (Binop (Times, Var "x", Num 21))))))
               "free_vars fun x -> x * 21";
    unit_test (same_vars set_x (free_vars (Fun ("y", (Binop (Times, Var "y", Var "x"))))))
               "free_vars fun x -> x * y";
    
    unit_test (same_vars empty (free_vars (Let (("x"), (Num 5), (Binop (LessThan, Var "x", Num 6))))))
               "free_vars let x = 5 in x < 6";
    unit_test (same_vars set_x (free_vars (Let (("y"), (Num 5), (Binop (LessThan, Var "x", Num 6))))))
               "free_vars let y = 5 in x < 6";
    unit_test (same_vars (vars_of_list ["f"]) (free_vars (Let
                                                         ("f", 
                                                          Fun ("x", Conditional (Binop(Equals, 
                                                              Var ("x"), Num(0)), Num(1),
                                                              Binop(Times, Var ("x"), App(Var("f"), 
                                                              Binop(Minus, Var ("x"), Num(1)))))), 
                                                          App(Var("f"), Num(4))))))
               "free_vars let f = fun x -> if x = 0 then 1 else x * f (x - 1) in f 4 ";

    unit_test (same_vars empty (free_vars (Letrec (("x"), (Num 5), (Binop (LessThan, Var "x", Num 6))))))
               "free_vars letrec x = 5 in x < 6";
    unit_test (same_vars set_x (free_vars (Letrec (("y"), (Num 5), (Binop (LessThan, Var "x", Num 6))))))
               "free_vars letrec y = 5 in x < 6";
    unit_test (same_vars empty (free_vars (Letrec 
                                            ("f", 
                                             Fun ("x", Conditional (Binop(Equals, 
                                                Var ("x"), Num(0)), Num(1),
                                                Binop(Times, Var ("x"), App(Var("f"), 
                                                Binop(Minus, Var ("x"), Num(1)))))), 
                                             App(Var("f"), Num(4))))))
               "free_vars let rec f = fun x -> if x = 0 then 1 else x * f (x - 1) in f 4 ";

    unit_test (same_vars empty (free_vars (App (Fun ("x", Binop (Plus, Var "x", Num 5)), Num 6)))) 
               "free_vars app (fun x -> x + 5) 6";
    unit_test (same_vars set_x_y (free_vars (App (Fun ("y", Binop (Plus, Var "x", Num 5)), Var "y")))) 
               "free_vars app (fun y -> x + 5) y";;
    


let subst_test () =
    unit_test ((subst "x" (Num 5) (Num 5)) = (Num 5))  
                "subst 5 with 5"; 

    unit_test ((subst "x" (Num 5) (Bool true)) = (Bool true))  
                "subst true with 5";

    unit_test ((subst "x" (Num 5) Raise) = Raise)  
                "subst raise with 5";

    unit_test ((subst "x" (Num 5) Unassigned) = Unassigned)  
                "subst ungassigned with 5";

    unit_test ((subst "x" (Num 5) (Var "x")) = (Num 5))  
                "subst free x with 5 in x";
    unit_test ((subst "y" (Num 5) (Var "x")) = (Var "x"))  
                "subst free y with 5 in x";

    unit_test ((subst "x" (Num 5) (Unop (Negate, Var "x"))) = (Unop (Negate, Num 5)))
                "subst -x with 5";

    unit_test ((subst "x" 
                      (Num 5) 
                      (Binop (Equals, Var "x", Num 5))) 
                    = Binop (Equals, Num 5, Num 5))
                "subst x = 5 with 5";
    unit_test ((subst "x" (
                      Num 5) 
                      (Binop 
                        (Equals, 
                         Var "x", 
                         Binop (Plus, Var "x", Num 1)))) 
                    = Binop (Equals, Num 5, Binop (Plus, Num 5, Num 1)))
                "subst x = x + 1 with 5";
    
    unit_test ((subst "x" (Num 5) (Conditional (Var "x", Num 8, Var "x"))) 
                    = (Conditional (Num 5, Num 8, Num 5)))
                "subst if x then 8 else x with 5";
    
    unit_test ((subst "x" (Num 5) (Fun ("x", Binop (Plus, Var "x", Num 2)))) 
                    = (Fun ("x", Binop (Plus, Var "x", Num 2))))
                "subst fun x -> x + 2 with x = 5";
    unit_test ((subst "x" (Num 5) (Fun ("y", Binop (Plus, Var "x", Num 2)))) 
                    = (Fun ("y", Binop (Plus, Num 5, Num 2))))
                "subst fun y -> x + 2 with x = 5";
    unit_test ((subst "x" 
                      (Binop (Plus, Var "y", Num 1)) 
                      (Fun ("y", Binop (Plus, Var "x", Num 2)))) 
                    = (Fun ("var0", Binop (Plus, Binop (Plus, Var "y", Num 1), Num 2))))
                "subst fun y -> x + 2 with x = y + 1";
    
    unit_test (subst "x" 
                      (Num 5)
                      (Let ("x", (Binop (Plus, Var "x", Num 2)), Var "x")) 
                    = ((Let ("x", (Binop (Plus, Num 5, Num 2)), Var "x"))))
                "subst let x = x + 2 in x with x = 5";
    unit_test (subst "x" 
                      (Num 5)
                      (Let ("y", (Binop (Plus, Var "x", Num 2)), Var "x")) 
                    = ((Let ("y", (Binop (Plus, Num 5, Num 2)), Num 5))))
                "subst let y = x + 2 in x with x = 5";
    unit_test (subst "x" 
                      (Binop (Plus, Var "y", Num 1))
                      (Let ("y", (Binop (Plus, Var "x", Num 2)), Var "x")) 
                    = ((Let ("var1", 
                         (Binop (Plus, (Binop (Plus, Var "y", Num 1)), Num 2)), 
                         (Binop (Plus, Var "y", Num 1))))))
                "subst let y = x + 2 in x with x = y + 1";
    
    unit_test (subst "x" 
                      (Num 5)
                      (Letrec ("x", (Binop (Plus, Var "x", Num 2)), Var "x")) 
                    = ((Letrec ("x", (Binop (Plus, Num 5, Num 2)), Var "x"))))
                "subst let rec x = x + 2 in x with x = 5";
    unit_test (subst "x" 
                      (Num 5)
                      (Letrec ("y", (Binop (Plus, Var "x", Num 2)), Var "x")) 
                     = ((Letrec ("y", (Binop (Plus, Num 5, Num 2)), Num 5))))
                "subst let rec y = x + 2 in x with x = 5";
    unit_test (subst "x" 
                      (Binop (Plus, Var "y", Num 1))
                      (Letrec ("y", (Binop (Plus, Var "x", Num 2)), Var "x")) 
                    = ((Letrec ("var2", 
                            (Binop (Plus, (Binop (Plus, Var "y", Num 1)), Num 2)), 
                            (Binop (Plus, Var "y", Num 1))))))
                "subst let rec y = x + 2 in x with x = y + 1";

    unit_test (subst "x" (Num 5) (App ((Fun ("x", Binop (Plus, Var "x", Num 2))), Num 1)) 
                    = (App ((Fun ("x", Binop (Plus, Var "x", Num 2))), Num 1)))
                "subst (fun x -> x + 2) 1 with x = 5";
    unit_test (subst "x" (Num 5) (App ((Fun ("y", Binop (Plus, Var "x", Num 2))), Var "x")) 
                    = (App ((Fun ("y", Binop (Plus, Num 5, Num 2))), Num 5)))
                "subst (fun y -> x + 2) x with x = 5" ;;


(* Helper function that converts expression into Env.Val *)
let value (exp : expr) = Env.Val exp ;;

let eval_s_test () = 
    let env = Env.empty () in

    unit_test (eval_s (Num 5) env = value (Num 5))
               "eval_s 5"; 
    
    unit_test (eval_s (Bool true) env = value (Bool true))
               "eval_s true"; 
    
    unit_test (try 
                eval_s (Var "x") env = value (Var "x")
               with EvalError "evaluation of unbound variable" -> true)
               "eval_s x"; 
    
    unit_test (eval_s (Fun ("x", Binop (Plus, Var "x", Num 5))) env 
                     = value (Fun ("x", Binop (Plus, Var "x", Num 5))))
               "eval_s fun x -> x + 5"; 
    
    unit_test (try 
                eval_s (Raise) env = value (Raise)
               with EvalError("error in evaluation") -> true)
               "eval_s Raise"; 

    unit_test (eval_s (Unop (Negate, Binop (Plus, Num 2, Num 5))) env 
                    = value (Num ~-7))
               "eval_s - (2 + 5)"; 

    unit_test (eval_s (Binop (Plus, Num 5, Num 3)) env 
                    = value (Num 8))
               "eval_s 3 * 5";
    unit_test (eval_s (Binop (Minus, Num 3, Num 5)) env 
                    = value (Num ~-2))
               "eval_s 3 - 5";           
    unit_test (eval_s (Binop (Times, Num 5, Num 3)) env 
                    = value (Num 15))
               "eval_s 3 * 5";
    unit_test (eval_s (Binop (Equals, Num 5, Num 3)) env 
                    = value (Bool false))
               "eval_s 3 = 5";     
    unit_test (eval_s (Binop (LessThan, Num 5, Num 3)) env 
                    = value (Bool false))
               "eval_s 5 < 3";
    unit_test (eval_s (Binop (Fplus, Float 5.0, Float 2.5)) env 
                    = value (Float 7.5))
               "eval_s 5.0 +. 2.5";
    unit_test (eval_s (Binop (Fminus, Float 5.0, Float 2.5)) env 
                    = value (Float 2.5))
               "eval_s 5.0 -. 2.5";
    unit_test (eval_s (Binop (Ftimes, Float 5.0, Float 2.5)) env 
                    = value (Float 12.5))
               "eval_s 5.0 *. 2.5";
    unit_test (eval_s (Binop (Equals, Float 2.5, Float 5.0)) env 
                    = value (Bool false))
               "eval_s 2.5 = 5";
    unit_test (eval_s (Binop (LessThan, Float 5.0, Float 2.5)) env 
                    = value (Bool false))
               "eval_s 5.0 = 2.5";
    unit_test (eval_l (Binop (Power, Float 2.0, Float 3.0)) env 
                    = value (Float 8.0))
               "eval_s 2.0 ** 3.0";
    
    unit_test (eval_s (Conditional ((Binop (Equals, Num 3, Num 3)), (Num 1), (Num 2))) env
                    = value (Num 1))
               "eval_s if 3 = 3 then 1 else 2";
    unit_test (eval_s (Conditional ((Binop (Equals, Num 4, Num 3)), (Num 1), (Num 2))) env
                    = value (Num 2))
               "eval_s if 4 = 3 then 1 else 2";
    
    unit_test (eval_s (Let ("x", (Binop (Plus, Num 5, Num 2)), Var "x")) env
                    = value (Num 7))
                "eval_s let x = 5 + 2 in x";

    unit_test (eval_s (Letrec ("x", (Binop (Plus, Num 5, Num 2)), Var "x")) env
                    = value (Num 7))
                "eval_s let rec x = 5 + 2 in x";
    unit_test (eval_s (Letrec 
                        ("f", 
                         Fun ("x", Conditional (Binop(Equals, 
                            Var ("x"), Num(0)), Num(1),
                            Binop(Times, Var ("x"), App(Var("f"), 
                            Binop(Minus, Var ("x"), Num(1)))))), 
                         App(Var("f"), Num(4)))) env 
                    = value (Num 24))
                "eval_s let rec f = fun x -> if x = 0 then 1 else x * f (x - 1) in f 4";
    
    unit_test (try 
                eval_s (Unassigned) env = value (Unassigned)
               with EvalError "unassigned cannot be evaluated" -> true)
               "eval_s unassigned"; 

    unit_test (eval_s (App ((Fun ("x", Binop (Times, Var "x", Num 10))), Num 11)) env
                    = value (Num 110))
                "eval_s (fun x -> x * 10) 11";
    unit_test (try 
                eval_s (App (Num 5, Num 11)) env = value (Num 0)
               with EvalError "function application on non-function" -> true)
               "eval_s 5 11";;
    
let env_module_tests () =
    let open Env in 
    let empty = Env.empty () in
    let env_x5 = Env.extend (Env.empty ()) "x" (ref (value (Num 5))) in
    let env_x6 = Env.extend (Env.empty ()) "x" (ref (value (Num 6))) in 
 

    unit_test (close (Fun ("x", Binop (Plus, Var "x", Num 5))) env_x5 
                = Closure (Fun ("x", Binop (Plus, Var "x", Num 5)), env_x5))
               "close [{x -> 5}, fun x -> x + 5]";

    unit_test (lookup env_x5 "x" = Env.Val (Num 5))
               "lookup x in {x -> 5}"; 
    unit_test (try 
                lookup empty "x" = Env.Val (Num 5)
               with EvalError "variable not found in environment" -> true)
               "lookup x in { }";
    
    unit_test (extend empty "x" (ref (Env.Val (Num 5))) = env_x5)
               "extend x = 5 in empty";
    unit_test (extend env_x5 "x" (ref (Env.Val (Num 6))) = env_x6)
               "extend x = 6 in {x -> 5}";;

let eval_d_test () =
    let empty = Env.empty () in
    let env_x5 = Env.extend (Env.empty ()) "x" (ref (value (Num 5))) in 

    unit_test (eval_d (Num 5) empty = value (Num 5))
               "eval_d 5"; 
    
    unit_test (eval_d (Bool true) empty = value (Bool true))
               "eval_d true"; 
    
    unit_test (try 
                eval_d (Var "x") empty = value (Var "x")
               with EvalError "variable not found in environment" -> true)
               "eval_d x"; 
    unit_test (eval_d (Var "x") env_x5 = value (Num 5))
               "eval_d x in x -> 5"; 
    
    unit_test (eval_d (Fun ("x", Binop (Plus, Var "x", Num 5))) empty 
                     = value (Fun ("x", Binop (Plus, Var "x", Num 5))))
               "eval_d fun x -> x + 5"; 
    unit_test (eval_d (Fun ("x", Binop (Plus, Var "x", Num 5))) env_x5 
                     = value (Fun ("x", Binop (Plus, Var "x", Num 5))))
               "eval_d fun x -> x + 5 in x -> 5"; 
    
    unit_test (try 
                eval_d (Raise) empty = value (Raise)
               with EvalError("error in evaluation") -> true)
               "eval_d Raise"; 

    unit_test (eval_d (Unop (Negate, Binop (Plus, Num 2, Num 5))) empty 
                    = value (Num ~-7))
               "eval_d - (2 + 5)"; 

    unit_test (eval_d (Binop (Plus, Num 5, Num 3)) env_x5 
                    = value (Num 8))
               "eval_d 3 * 5";
    unit_test (eval_d (Binop (Minus, Num 3, Num 5)) empty 
                    = value (Num ~-2))
               "eval_d 3 - 5";           
    unit_test (eval_d (Binop (Times, Num 5, Num 3)) empty 
                    = value (Num 15))
               "eval_d 3 * 5";
    unit_test (eval_d (Binop (Equals, Num 5, Num 3)) env_x5 
                    = value (Bool false))
               "eval_d 3 = 5";     
    unit_test (eval_d (Binop (LessThan, Num 5, Num 3)) empty 
                    = value (Bool false))
               "eval_d 5 < 3";
    unit_test (eval_d (Binop (Fplus, Float 5.0, Float 2.5)) empty 
                    = value (Float 7.5))
               "eval_d 5.0 +. 2.5";
    unit_test (eval_d (Binop (Fminus, Float 5.0, Float 2.5)) empty 
                    = value (Float 2.5))
               "eval_d 5.0 -. 2.5";
    unit_test (eval_d (Binop (Ftimes, Float 5.0, Float 2.5)) empty 
                    = value (Float 12.5))
               "eval_d 5.0 *. 2.5";
    unit_test (eval_d (Binop (LessThan, Float 2.5, Float 5.0)) empty 
                    = value (Bool true))
               "eval_d 2.5 < 5";
    unit_test (eval_d (Binop (Equals, Float 5.0, Float 2.5)) empty 
                    = value (Bool false))
               "eval_d 5.0 = 2.5";
    unit_test (eval_d (Binop (Power, Float 2.0, Float 3.0)) empty 
                    = value (Float 8.0))
               "eval_d 2.0 ** 3.0";
    
    unit_test (eval_d (Conditional ((Binop (Equals, Num 3, Num 3)), (Num 1), (Num 2))) empty
                    = value (Num 1))
               "eval_d if 3 = 3 then 1 else 2";
    unit_test (eval_d (Conditional ((Binop (Equals, Num 4, Num 3)), (Num 1), (Num 2))) env_x5
                    = value (Num 2))
               "eval_d if 4 = 3 then 1 else 2";
    
    unit_test (eval_d (Let ("x", (Binop (Plus, Num 5, Num 2)), Var "x")) empty
                    = value (Num 7))
                "eval_d let x = 5 + 2 in x";
    unit_test (eval_d (Let ("x", (Binop (Plus, Num 5, Num 2)), Var "x")) env_x5
                    = value (Num 7))
                "eval_d let x = 5 + 2 in x";
    unit_test (eval_d (Let ("x", (Binop (Plus, Num 5, Num 2)), Var "x")) env_x5
                    = value (Num 7))
                "eval_d let x = 5 + 2 in x";
    unit_test (eval_d (Let ("x", 
                            Num 1, 
                            Let ("f", 
                                 Fun ("y", 
                                      Binop (Plus, Var "x", 
                                      Var "y")), 
                                 Let ("x", 
                                      Num 2, 
                                      App (Var "f", Num 3)))))
                       empty 
                = value (Num 5))
               "eval_d let x = 1 in let f = fun y -> x + y in let x = 2 in f 3";
    unit_test (eval_d (Letrec ("x", (Binop (Plus, Num 5, Num 2)), Var "x")) empty
                    = value (Num 7))
                "eval_d let rec x = 5 + 2 in x with x -> 5";
    unit_test (eval_d (Letrec ("x", (Binop (Plus, Num 5, Num 2)), Var "x")) env_x5
                    = value (Num 7))
                "eval_d let rec x = 5 + 2 in x with x -> 5";
    unit_test (eval_d (Letrec 
                        ("f", 
                         Fun ("x", Conditional (Binop(Equals, 
                            Var ("x"), Num(0)), Num(1),
                            Binop(Times, Var ("x"), App(Var("f"), 
                            Binop(Minus, Var ("x"), Num(1)))))), 
                         App(Var("f"), Num(4)))) empty 
                    = value (Num 24))
                "eval_d let rec f = fun x -> if x = 0 then 1 else x * f (x - 1) in f 4";
    
    unit_test (try 
                eval_d (Unassigned) empty = value (Unassigned)
               with EvalError "unassigned cannot be evaluated" -> true)
               "eval_d unassigned"; 

    unit_test (eval_d (App ((Fun ("x", Binop (Times, Var "x", Num 10))), Num 11)) empty
                    = value (Num 110))
                "eval_d (fun x -> x * 10) 11";
    unit_test (eval_d (App ((Fun ("x", Binop (Times, Var "x", Num 10))), Num 11)) env_x5
                    = value (Num 110))
                "eval_d (fun x -> x * 10) 11 with x -> 5";
    unit_test (eval_d (App ((Fun ("y", Binop (Times, Var "x", Num 10))), Num 11)) 
                        (Env.extend (Env.empty ()) "x" (ref (value (Num 5))))
                    = value (Num 50))
                "eval_d (fun y -> x * 10) 11 with x -> 5";
    unit_test (try 
                eval_d (App (Num 5, Num 11)) empty = value (Num 0)
               with EvalError "function application on non-function" -> true)
               "eval_d 5 11";;

let eval_l_test () =
    let empty = Env.empty () in
    let env_x5 = Env.extend (Env.empty ()) "x" (ref (value (Num 5))) in 

    unit_test (eval_l (Num 5) empty = value (Num 5))
               "eval_l 5"; 
    
    unit_test (eval_l (Bool true) empty = value (Bool true))
               "eval_l true"; 
    
    unit_test (try 
                eval_l (Var "x") empty = value (Var "x")
               with EvalError "variable not found in environment" -> true)
               "eval_l x"; 
    unit_test (eval_l (Var "x") env_x5 = value (Num 5))
               "eval_l x in x -> 5"; 
    
    unit_test (eval_l (Fun ("x", Binop (Plus, Var "x", Num 5))) empty 
                     = Env.Closure ((Fun ("x", Binop (Plus, Var "x", Num 5))), empty))
               "eval_l fun x -> x + 5"; 
    unit_test (eval_l (Fun ("x", Binop (Plus, Var "x", Num 5))) env_x5 
                     = Env.Closure ((Fun ("x", Binop (Plus, Var "x", Num 5))), env_x5))
               "eval_l fun x -> x + 5 in x -> 5"; 
    
    unit_test (try 
                eval_l (Raise) empty = value (Raise)
               with EvalError("error in evaluation") -> true)
               "eval_l Raise"; 

    unit_test (eval_l (Unop (Negate, Binop (Plus, Num 2, Num 5))) empty 
                    = value (Num ~-7))
               "eval_l - (2 + 5)"; 

    unit_test (eval_l (Binop (Plus, Num 5, Num 3)) env_x5 
                    = value (Num 8))
               "eval_l 3 * 5";
    unit_test (eval_l (Binop (Minus, Num 3, Num 5)) empty 
                    = value (Num ~-2))
               "eval_l 3 - 5";           
    unit_test (eval_l (Binop (Times, Num 5, Num 3)) empty 
                    = value (Num 15))
               "eval_l 3 * 5";
    unit_test (eval_l (Binop (Equals, Num 5, Num 3)) env_x5 
                    = value (Bool false))
               "eval_l 3 = 5";     
    unit_test (eval_l (Binop (LessThan, Num 5, Num 3)) empty 
                    = value (Bool false))
               "eval_l 5 < 3";
    unit_test (eval_l (Binop (Fplus, Float 5.0, Float 2.5)) empty 
                    = value (Float 7.5))
               "eval_l 5.0 +. 2.5";
    unit_test (eval_l (Binop (Fminus, Float 5.0, Float 2.5)) empty 
                    = value (Float 2.5))
               "eval_l 5.0 -. 2.5";
    unit_test (eval_l (Binop (Ftimes, Float 5.0, Float 2.5)) empty 
                    = value (Float 12.5))
               "eval_l 5.0 *. 2.5";
    unit_test (eval_l (Binop (Equals, Float 5.0, Float 2.5)) empty 
                    = value (Bool false))
               "eval_l 5.0 = 2.5";
    unit_test (eval_l (Binop (LessThan, Float 5.0, Float 2.5)) empty 
                    = value (Bool false))
               "eval_l 5.0 < 2.5"; 
    unit_test (eval_l (Binop (Power, Float 2.0, Float 3.0)) empty 
                    = value (Float 8.0))
               "eval_l 2.0 ** 3.0";
    
    unit_test (eval_l (Conditional ((Binop (Equals, Num 3, Num 3)), (Num 1), (Num 2))) empty
                    = value (Num 1))
               "eval_l if 3 = 3 then 1 else 2";
    unit_test (eval_l (Conditional ((Binop (Equals, Num 4, Num 3)), (Num 1), (Num 2))) env_x5
                    = value (Num 2))
               "eval_l if 4 = 3 then 1 else 2";
    
    unit_test (eval_l (Let ("x", (Binop (Plus, Num 5, Num 2)), Var "x")) empty
                    = value (Num 7))
                "eval_l let x = 5 + 2 in x";
    unit_test (eval_l (Let ("x", (Binop (Plus, Num 5, Num 2)), Var "x")) env_x5
                    = value (Num 7))
                "eval_l let x = 5 + 2 in x with x -> 5";
    unit_test (eval_l (Let ("x", 
                            Num 1, 
                            Let ("f", 
                                 Fun ("y", 
                                      Binop (Plus, Var "x", 
                                      Var "y")), 
                                 Let ("x", 
                                      Num 2, 
                                      App (Var "f", Num 3)))))
                       (Env.empty ())
                = value (Num 4))
               "eval_l let x = 1 in let f = fun y -> x + y in let x = 2 in f 3";

    unit_test (eval_l (Letrec ("x", (Binop (Plus, Num 5, Num 2)), Var "x")) empty
                    = value (Num 7))
                "eval_l let rec x = 5 + 2 in x with x -> 5";
    unit_test (eval_l (Letrec ("x", (Binop (Plus, Num 5, Num 2)), Var "x")) env_x5
                    = value (Num 7))
                "eval_l let rec x = 5 + 2 in x with x -> 5";
    unit_test (eval_l (Letrec 
                        ("f", 
                         Fun ("x", Conditional (Binop(Equals, 
                            Var ("x"), Num(0)), Num(1),
                            Binop(Times, Var ("x"), App(Var("f"), 
                            Binop(Minus, Var ("x"), Num(1)))))), 
                         App(Var("f"), Num(4)))) empty 
                    = value (Num 24))
                "eval_l let rec f = fun x -> if x = 0 then 1 else x * f (x - 1) in f 4";
    
    unit_test (try 
                eval_l (Unassigned) empty = value (Unassigned)
               with EvalError "unassigned cannot be evaluated" -> true)
               "eval_l unassigned"; 

    unit_test (eval_l (App ((Fun ("x", Binop (Times, Var "x", Num 10))), Num 11)) empty
                    = value (Num 110))
                "eval_l (fun x -> x * 10) 11";
    unit_test (eval_l (App ((Fun ("x", Binop (Times, Var "x", Num 10))), Num 11)) env_x5
                    = value (Num 110))
                "eval_l (fun x -> x * 10) 11 with x -> 5";
    unit_test (eval_l (App ((Fun ("y", Binop (Times, Var "x", Num 10))), Num 11)) 
                        (Env.extend (Env.empty ()) "x" (ref (value (Num 5))))
                    = value (Num 50))
                "eval_l (fun y -> x * 10) 11 with x -> 5";
    unit_test (try 
                eval_l (App (Num 5, Num 11)) empty = value (Num 0)
               with EvalError "function application on non-function" -> true)
               "eval_l 5 11";;
    

let _ = free_vars_test () ;;
let _ = subst_test () ;;
let _ = env_module_tests () ;;
let _ = eval_s_test () ;;
let _ = eval_d_test () ;;
let _ = eval_l_test () ;;
