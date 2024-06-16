namespace MinTheta

module Program =

  open Core
  open Parse
  open Parse.Input
  open Parse.Tokenizer
  open System.IO

  [<EntryPoint>]
  let main argv =
    use stream = new FileStream (argv[0], FileMode.Open, FileAccess.Read)
    use reader = new StreamReader (stream)
    InputOfStream reader
    |> Tokenizer
    |> parseMod
    |> checkMod
    0