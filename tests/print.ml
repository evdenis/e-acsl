module Printer_extension(X:Printer.PrinterClass) = struct

  class printer = object
    inherit Printer.extensible_printer () as super

    method! global fmt g =
      let loc, _ = Cil_datatype.Global.loc g in
      let file = loc.Lexing.pos_fname in
      if file = "" || List.exists
        (fun s -> Filepath.normalize s = file)
        (Kernel.Files.get ())
      then super#global fmt g

  end

end

let () = Printer.update_printer (module Printer_extension)
