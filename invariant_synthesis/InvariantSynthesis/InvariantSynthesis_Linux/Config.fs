﻿module Config

    /// <summary>
    /// Executable of the parser
    /// </summary>
    let parser_cmd = "parser.native"
    /// <summary>
    /// Arguments for the parser. %IN% %OUT% %ERR% can be used.
    /// </summary>
    let parser_args = "all %IN% %OUT% %ERR%"
    /// <summary>
    /// Temporary file for the output of the parser.
    /// </summary>
    let parser_output_path = "parser.out"
    /// <summary>
    /// Temporary file for the error output of the parser.
    /// </summary>
    let parser_error_path = "parser.err"
