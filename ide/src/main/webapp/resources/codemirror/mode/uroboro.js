CodeMirror.defineMode("uroboro", function(_config, modeConfig) {

	function switchState(source, setState, f) {
    	setState(f);
    	return f(source, setState);
  	}


  	var digitRE = /[0-9]/;
  	var smallRE = /[a-z]/;
  	var largeRE = /[A-Z]/;
  	var idRE = /[a-z_A-Z0-9']/;
  	var whiteCharRE = /[ \t\v\f]/;
  	var specialRE = /[()[\]{}]/;

  	function normal(source, setState) {
  		
  		if (source.eatWhile(whiteCharRE)) {
      		return null;
    	}

  		var ch = source.next();
  		if(ch == '/' && source.eat('*')){
  			var t = "comment";
  			return switchState(source, setState, ncomment(t, 1));
  		}

  	
      	if (ch == '/' && source.eat('/')) {
	        source.eatWhile('/');
	        //if (!source.eat(symbolRE)) {
	          source.skipToEnd();
	          return "comment";
	        //}
        }

        if(specialRE.test(ch)){
        	return "bracket";
        }

        if (ch == '"') {
      		return switchState(source, setState, stringLiteral);
    	}

        if (largeRE.test(ch)) {
	    	source.eatWhile(idRE);
	      	if (source.eat('.')) {
	        	return "qualifier";
	      	}
	      	return "typename";
	    }

	    if (smallRE.test(ch)) {
	      	source.eatWhile(idRE);
	      	if (source.peek() === '[') {
	        	return "cons";
	      	}
	      	if (source.peek()==='(') {
	        	return "destructor";
	      	}
	      	
	      	return "variable";
	    }

	    if(ch == '_') {
	    	source.eatWhile(idRE);
	    	if (source.peek()==='(') {
	    		/*var c = source.next();
	    		if (source.peek()==='(') {
		        	return "local-function";
		      	}*/
		      	
	        	return "local-destructor";
	      	}
	      	if (source.peek() === '[') {
	      		/*var c = source.next();
	      		if (source.peek() === '[') {
		        	return "local-function";
		      	}*/
	        	return "local-cons";
	      	}
	      	return "match-comatch";
	    }

      	if (digitRE.test(ch)) {
      
		    source.eatWhile(digitRE);
		   		    
		    return "number";
    	}

      	return "error";
  	}

  	function ncomment(type, nest) {
	    if (nest == 0) {
	      return normal;
	    }
	    return function(source, setState) {
	      var currNest = nest;
	      while (!source.eol()) {
	        var ch = source.next();
	        if (ch == '/' && source.eat('*')) {
	          ++currNest;
	        }
	        else if (ch == '*' && source.eat('/')) {
	          --currNest;
	          if (currNest == 0) {
	            setState(normal);
	            return type;
	          }
	        }
	      }
	      setState(ncomment(type, currNest));
	      return type;
	    };
	 }

	function stringLiteral(source, setState) {
	    while (!source.eol()) {
		      var ch = source.next();
		      if (ch == '"') {
		        setState(normal);
		        return "string";
		      }
		      if (ch == '\\') {
		        if (source.eol() || source.eat(whiteCharRE)) {
		          setState(stringGap);
		          return "string";
		        }
		       
		      }
	    }
	    setState(normal);
	    return "error";
	 }

	function stringGap(source, setState) {
	    if (source.eat('\\')) {
	      return switchState(source, setState, stringLiteral);
	    }
	    source.next();
	    setState(normal);
	    return "error";
  	}

	var wellKnownWords = (function() {
	    var wkw = {};
	    function setType(t) {
	      return function () {
	        for (var i = 0; i < arguments.length; i++)
	          wkw[arguments[i]] = t;
	      };
	    }

	    setType("keyword")(
	      "data", "codata", "where", "in", "let", "match", "comatch", "fun",
	       "case", "cocase", "gfun", "cfun", "using", "with", "returning");


	    setType("builtin")(".", ":", "=", "=>");

	    var override = modeConfig.overrideKeywords;
	    if (override) for (var word in override) if (override.hasOwnProperty(word))
	      wkw[word] = override[word];

	    return wkw;
  	})();

  	return {
	    startState: function ()  { return { f: normal }; },
	    copyState:  function (s) { return { f: s.f }; },

	    token: function(stream, state) {
	      var t = state.f(stream, function(s) { state.f = s; });
	      var w = stream.current();
	      return wellKnownWords.hasOwnProperty(w) ? wellKnownWords[w] : t;
	    },

	    blockCommentStart: "/*",
	    blockCommentEnd: "*/",
	    lineComment: "//"
  	};
});

CodeMirror.defineMIME("text/x-uroboro", "uroboro");
