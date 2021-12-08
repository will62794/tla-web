function tlaplusMode(obj, modeConfig){
    console.log(obj);
    console.log(modeConfig);

    var external = {
        startState: function(basecolumn) {
          return {
            tokenize: null,
            scope: {offset:basecolumn || 0, type:"coffee", prev: null, align: false},
            prop: false,
            dedent: 0
          };
        },
    
        token: function(stream, state) {
        console.log(stream);
        stream.sol();
        stream.next();
        //   var fillAlign = state.scope.align === null && state.scope;
        //   if (fillAlign && stream.sol()) fillAlign.align = false;
    
        //   var style = tokenLexer(stream, state);
        //   if (style && style != "comment") {
        //     if (fillAlign) fillAlign.align = true;
        //     state.prop = style == "punctuation" && stream.current() == "."
        //   }

         // TODO: Customize this to proper coloring.
         return "none";
         return "keyword";
         return "error";
         return "variable";
    
          return style;
        },
    
        indent: function(state, text) {
          if (state.tokenize != tokenBase) return 0;
          var scope = state.scope;
          var closer = text && "])}".indexOf(text.charAt(0)) > -1;
          if (closer) while (scope.type == "coffee" && scope.prev) scope = scope.prev;
          var closes = closer && scope.type === text.charAt(0);
          if (scope.align)
            return scope.alignOffset - (closes ? 1 : 0);
          else
            return (closes ? scope.prev : scope).offset;
        },
    
        lineComment: "#",
        fold: "indent"
      };
    return external;
}

// CodeMirror.defineMode("tlaplus", tlaplusMode);