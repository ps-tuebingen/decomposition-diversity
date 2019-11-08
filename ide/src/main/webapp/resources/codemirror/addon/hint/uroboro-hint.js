(function(mod) {
  if (typeof exports == "object" && typeof module == "object") // CommonJS
    mod(require("../../lib/codemirror"));
  else if (typeof define == "function" && define.amd) // AMD
    define(["../../lib/codemirror"], mod);
  else // Plain browser env
    mod(CodeMirror);
})(function(CodeMirror) {
  "use strict";

  function forEach(arr, f) {
    for (var i = 0, e = arr.length; i < e; ++i) f(arr[i]);
  }

  function arrayContains(arr, item) {
    if (!Array.prototype.indexOf) {
      var i = arr.length;
      while (i--) {
        if (arr[i] === item) {
          return true;
        }
      }
      return false;
    }
    return arr.indexOf(item) != -1;
  }

  function scriptHint(editor, keywords, getToken) {
    // Find the token at the cursor
    var cur = editor.getCursor(), token = getToken(editor, cur); 
    // If it's not a 'word-style' token, ignore the token.

    if (!/^[\w$_]*$/.test(token.string)) {
        token = tprop = {start: cur.ch, end: cur.ch, string: "", state: token.state,
                         className: token.string == "." ? "uroboro-type" : null};
    } else if (token.end > cur.ch) {
      token.end = cur.ch;
      token.string = token.string.slice(0, cur.ch - token.start);
    }

    var tprop = token;

    if (!context) var context = [];
    context.push(tprop);

    var completionList = getCompletions(token, context, keywords);
    completionList = completionList.sort();
    
    return {list: completionList,
            from: CodeMirror.Pos(cur.line, token.start),
            to: CodeMirror.Pos(cur.line, token.end)};
  }

  function uroboroHint(editor) {
    return scriptHint(editor, uroboroKeywordsL, function (e, cur) {return e.getTokenAt(cur);});
  }
  CodeMirror.registerHelper("hint", "uroboro", uroboroHint);

  var uroboroKeywordsL = ["data"
                          , "codata"
                          , "where"
                          , "in"
                          , "let"
                          , "match"
                          , "comatch"
                          , "fun"
                          , "cfun"
                          , "gfun"
                          , "case"
                          , "cocase"
                          , "using"
                          , "with"
                          , "returning"
                         ];

  function getCompletions(token, context,keywords) {
    var found = [], start = token.string;
    function maybeAdd(str) {
      if (str.lastIndexOf(start, 0) == 0 && !arrayContains(found, str)) found.push(str);
    }

    function gatherCompletions(_obj) {
        forEach(uroboroKeywordsL, maybeAdd);

    }

    if (context) {
      // If this is a property, see if it belongs to some object we can
      // find in the current environment.
      var obj = context.pop(), base;

      if (obj.type == "variable")
          base = obj.string;
      else if(obj.type == "variable-2")
          base = obj.string;
      else if(obj.type == "variable-3")
          base = obj.string;
      

      while (base != null && context.length)
        base = base[context.pop().string];
      if (base != null) gatherCompletions(base);
    } else {
       maybeAdd(start);
       forEach(keywords, maybeAdd);

    }

    return found;
  }
});
