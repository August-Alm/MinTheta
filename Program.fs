namespace MinTheta

module Program =

  open Core
  open Parse
  open Parse.Input
  open Parse.Tokenizer
  open System.IO

  [<EntryPoint>]
  let main argv =
    let t = parseTermFromString "λA.λs.λz.([s : θs.λx.[[x : A] ⇓ A]] [z : A])"
    //let t = parseTermFromString "λA.λs.λz.[([s : θs.λx.[[x : A] ⇓ A]] [z : A]) ⇓ A]"
    let m = Mod ()
    printfn "%s" (show (quote (hoas m [] t)))//(normalize m t))
    use stream = new FileStream (argv[0], FileMode.Open, FileAccess.Read)
    use reader = new StreamReader (stream)
    InputOfStream reader
    |> Tokenizer
    |> parseMod
    |> checkMod
    //let m =
    //  InputOfStream reader
    //  |> Tokenizer
    //  |> parseMod
    //let unr t = term [] (unref m (hoas m [] t))
    //for def in m.Defs do
    //  printfn "Gonna normalize %s" def.Name
    //  //printfn "%s" (normalize m def.Term |> show)
    //  printfn "%s" (normalize m def.Term |> show)
    0