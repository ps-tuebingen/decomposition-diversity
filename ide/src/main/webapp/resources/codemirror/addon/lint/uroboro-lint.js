// CodeMirror, copyright (c) by Marijn Haverbeke and others
// Distributed under an MIT license: https://codemirror.net/LICENSE

// Depends on csslint.js from https://github.com/stubbornella/csslint

// declare global: CSSLint

(function(mod) {
  if (typeof exports == "object" && typeof module == "object") // CommonJS
    mod(require("../../lib/codemirror"));
  else if (typeof define == "function" && define.amd) // AMD
    define(["../../lib/codemirror"], mod);
  else // Plain browser env
    mod(CodeMirror);
})(function(CodeMirror) {
"use strict";

CodeMirror.registerHelper("lint", "uroboro", function(text, options) {
  var found = [];

  var result = verify(text);
  console.log(result)
  if(result.status === 'success'){

    if(text===''){
      $("#refuncBtn").attr("disabled", true);
      $("#defuncBtn").attr("disabled", true);
      $("#stepp").attr("disabled", true);
      $("#transformation").attr("disabled", true);
      $("#refactor").attr("disabled", true);
      $("#source").attr("disabled", true);
    } else {
      var warnings = JSON.parse(result.data.errors);
      var element = document.getElementById('runResult');

      var msg;
      if(warnings.length===0){
          if(element.classList.contains("succW")){
            element.classList.remove("succW");
          }
           if(element.classList.contains("error")){
            element.classList.remove("error");
          }
          element.classList.add('Succ');
          msg = "Program compiled successfully";
      }else{
         if(element.classList.contains("Succ")){
            element.classList.remove("Succ");
          }
          if(element.classList.contains("error")){
            element.classList.remove("error");
          }
        element.classList.add('succW');
        msg = "Program compiled successfully but with warnings";
      }

      $('#runResult').val(msg);
      //window.program = JSON.parse(result.data);
      localStorage.setItem("data", result.data.data);
      localStorage.setItem("codata", result.data.codata);
      $("#refuncBtn").attr("disabled", false);
      $("#defuncBtn").attr("disabled", false);
      $("#stepp").attr("disabled", false);
      $("#transformation").attr("disabled", false);
      $("#refactor").attr("disabled", false);
      $("#source").attr("disabled", false);
      var cmLines = document.querySelectorAll('.CodeMirror-line');
      for (var cml of cmLines) {
        console.log(cml);
        var dest = cml.querySelectorAll('.cm-destructor');
        var cons = cml.querySelectorAll('.cm-cons');
        var lDest = cml.querySelectorAll('.cm-local-destructor');
        var lCons = cml.querySelectorAll('.cm-local-cons');
        for(var d of dest){
          // d.addEventListener('mouseenter', function (e) {
           d.addEventListener('mouseover', function (e) {
            console.log(this.textContent)
            var name = this.textContent;
            console.log(result.data.consAndDesMap[name])
            if(result.data.consAndDesMap[name] == undefined){
              $('.preview').css('visibility', 'hidden');
            }else {
              $('.preview').css('visibility', 'visible');
              $('.preview').empty().html(result.data.consAndDesMap[name]); 
            }
            
          }, false); 

          // d.addEventListener('mouseleave', function (e) {
          d.addEventListener('mouseout', function (e) {
            //console.log(this.textContent)
            $('.preview').css('visibility', 'hidden');
            
          }, false); 
        }

        for(var d of lDest){
          // d.addEventListener('mouseenter', function (e) {
          d.addEventListener('mouseover', function (e) {
            console.log(this.textContent)
            var name = this.textContent;
            console.log(result.data.consAndDesMap[name])
            if(result.data.consAndDesMap[name] == undefined){
              $('.preview').css('visibility', 'hidden');
            }else {
              $('.preview').css('visibility', 'visible');
              $('.preview').empty().html(result.data.consAndDesMap[name]); 
            }
            
          }, false); 

          // d.addEventListener('mouseleave', function (e) {
          d.addEventListener('mouseout', function (e) {
            //console.log(this.textContent)
            $('.preview').css('visibility', 'hidden');
            
          }, false); 
        }

        for(var c of cons){
          // c.addEventListener('mouseenter', function (e) {
          c.addEventListener('mouseover', function (e) {
            console.log(this.textContent)
            var name = this.textContent;
            if(result.data.consAndDesMap[name] == undefined){
              $('.preview').css('visibility', 'hidden');
            } else {
              $('.preview').css('visibility', 'visible');
              $('.preview').empty().html(result.data.consAndDesMap[name]);  
            }
           
          }, false); 

          // c.addEventListener('mouseleave', function (e) {
          c.addEventListener('mouseout', function (e) {
            //console.log(this.textContent)
            $('.preview').css('visibility', 'hidden');
            
          }, false); 
        }

        for(var c of lCons){
          // c.addEventListener('mouseenter', function (e) {
          c.addEventListener('mouseover', function (e) {
            console.log(this.textContent)
            var name = this.textContent;
            if(result.data.consAndDesMap[name] == undefined){
              $('.preview').css('visibility', 'hidden');
            } else {
              $('.preview').css('visibility', 'visible');
              $('.preview').empty().html(result.data.consAndDesMap[name]);  
            }
           
          }, false); 

          // c.addEventListener('mouseleave', function (e) {
          c.addEventListener('mouseout', function (e) {
            //console.log(this.textContent)
            $('.preview').css('visibility', 'hidden');
            
          }, false); 
        }
        
        
      }
    }
    if(result.data.errors.length===0)
      return found;
  }else{
    var element = document.getElementById('runResult');
    if(element.classList.contains("Succ")){
      element.classList.remove("Succ");
    }
    if(element.classList.contains("succW")){
      element.classList.remove("succW");
    }
    element.classList.add('error');
    $('#runResult').val("COMPILATION ABORTED")
    
    $("#refuncBtn").attr("disabled", true);
    $("#defuncBtn").attr("disabled", true);
    $("#stepp").attr("disabled", true);
    $("#transformation").attr("disabled", true);
    $("#refactor").attr("disabled", true);
    $("#source").attr("disabled", true);
  }
  
  var messages = JSON.parse(result.data.errors);
  console.log("results = " + JSON.stringify(messages));
  for ( var i = 0; i < messages.length; i++) {
    var message = messages[i];
    var startLine = message.line -1, endLine = message.stopLine -1, startCol = message.col, endCol = message.stopCol+1;
    found.push({
      from: CodeMirror.Pos(startLine, startCol),
      to: CodeMirror.Pos(endLine, endCol),
      message: message.message,
      severity : message.severity
    });
  }
  
  
  console.log("found = " + found);
  return found;
});

});

function verify(text) {
  if(text === '')
    return {status: "success", data:{numOfErrors:0, errors:[]}};
  var params = {
      source : text
  }
    var host = window.location.hostname
    var port = window.location.port
  return JSON.parse($.ajax({
    type : "POST",
    contentType : "application/json",
    url : "http://" + host + ":" + port + "/decompositiondiversity/api/compile",
    data : JSON.stringify(params),
    dataType : 'json',
    global: false,
    async: false,
    success : function(result) {
      return result;
      
      
    },
    error : function(e) {
      console.log("ERROR: ", e);
      $('#runResult').val(JSON.stringify(e));   
    }
  }).responseText);
}
