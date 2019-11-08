/**
 * 
 */

$(document).ready(function(){
	var editableCodeMirror = CodeMirror.fromTextArea(document.getElementById('cm_editor'), {
    	autoCloseBrackets: true,
		lineNumbers : true,
		lineWrapping: true,
 	 	matchBrackets: true,
  		mode: 'uroboro',
  		styleActiveLine: true,
  		theme: 'uroboro',
  		extraKeys: {"Ctrl-Space": "autocomplete"},
  		highlightSelectionMatches: {showToken: /\w/, annotateScrollbar: true}
    }); 
	
	var readOnlyCodeMirror = CodeMirror.fromTextArea(document.getElementById('cmEditor_ReadOnly'), {
		 	autoCloseBrackets: true,
		 	lineNumbers : true,
			lineWrapping: true,
	 	 	matchBrackets: true,
	  		mode: 'uroboro',
	  		styleActiveLine: true,
	  		theme: 'uroboro',
	  		highlightSelectionMatches: {showToken: /\w/, annotateScrollbar: true},
	        readOnly: true
	    });  
	    
	    Notification.init({
	        "selector": ".bb-alert"
	    });
	    
	    
	    $("#run").click(function(event){
			// Prevent the form from submitting via the browser.
			event.preventDefault();
			if(editableCodeMirror.getValue() === ''){
				Notification.show("Please insert your Expression!")
			} else{
				$("#run").attr("disabled", true);
				editableCodeMirror.setOption("readOnly",true);
				let expression = editableCodeMirror.getValue();
				run(expression,editableCodeMirror,readOnlyCodeMirror,allExpr,current);
			}
		});
	    
	    $("#step").click(function(event){
			// Prevent the form from submitting via the browser.
			event.preventDefault();
			nextStep(editableCodeMirror,readOnlyCodeMirror,allExpr);
		});

		$("#prev").click(function(event){
			// Prevent the form from submitting via the browser.
			event.preventDefault();
			prevStep(editableCodeMirror,readOnlyCodeMirror,allExpr);
		});
	    
	    $("#stop").click(function(event){
	    	editableCodeMirror.setValue("");
	    	editableCodeMirror.setOption("readOnly",false);
	    	readOnlyCodeMirror.setValue("");
	    	$("#run").attr("disabled", false);
	    	$("#stop").attr("disabled", true);
	    	$("#step").attr("disabled", true);
	    	$("#prev").attr("disabled", true);
	    	setCurr(0);
	    	setAllExpr([]);
	    	setHasNext(true);
	    	// Prevent the form from submitting via the browser.
			event.preventDefault();
		});
	    
		  $('[data-toggle="tooltip"]').click(function () {
	          $('[data-toggle="tooltip"]').tooltip("hide");

	      });
});

var allExpr = [];
var current = 0;

var hasNext = true;

function setCurr(val){
	current = val;
}

function getCurr(){
	return this.current;
}

function setAllExpr(val){
	allExpr=val;
	
}
function getHasNext(){
	return this.hasNext;
}

function setHasNext(val){
	this.hasNext = val;
}

var Notification = (function() {
    "use strict";

    var elem,
        hideHandler,
        that = {};

    that.init = function(options) {
        elem = $(options.selector);
    };

    that.show = function(text) {
        clearTimeout(hideHandler);

        elem.find("span").html(text);
        elem.fadeIn();

        hideHandler = setTimeout(function() {
            that.hide();
        }, 4000);
    };

    that.hide = function() {
        elem.fadeOut();
    };

    return that;
}());

$(function () {
	  $('[data-toggle="tooltip"]').tooltip();
})
/*------------------------------------------------------
---- Evaluate expression								----
-------------------------------------------------------*/
function run(expression,cmEditor,resEditor,allExpr,current){
	
	// var cursor = cmEditor.getCursor();
	// var expression = cmEditor.getLine(cursor.line);
	console.log(expression);
	
	var cmd = {
			expr : expression
	}
	
	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/exprEval",
		data : JSON.stringify(cmd),
		dataType : 'json',
		success : function(result) {
//			resEditor.focus();
			// resEditor.setCursor(cursor);
			// if(cursor.line == 0){
			// 	if(result.status === 'error'){
			// 		Notification.show(result.data);
			// 	}else{
			// 		resEditor.setValue(result.data);
			// 	}
				
			// } else {
			// 	resEditor.replaceRange('\n'+result.data,cursor);
			// }
			if(allExpr.length == 0){
				if(result.status === 'error'){
					Notification.show(result.data);
				}	
			}
			
			if(result.status !== 'error'){
				$("#step").attr("disabled", false);
				cmEditor.setValue(expression);
				resEditor.setValue(result.data);
				allExpr.push({
					expr: expression,
					res: result.data
				});
				
				if(allExpr.length>1)
					$("#prev").attr("disabled", false);
				var lineTokens = cmEditor.getLineTokens(0);
				var len = lineTokens.length;
				cmEditor.setCursor(lineTokens[len-1].end);
				setCurr(allExpr.length-1);
				console.log(getCurr() + " ==> " +allExpr);
				console.log(cmEditor.getLine(0)+" "+resEditor.getLine(0))

				console.log(cmEditor.getLine(0)+" "+resEditor.getLine(0))
				
				var tokens = getStartToken(cmEditor.getLineTokens(0),resEditor.getLineTokens(0));
				cmEditor.getDoc().markText({line:0,ch:tokens.start},{line:0,ch:tokens.end},{css: "background-color: #d5fdd5"});

				var tokensRe = getStartToken(resEditor.getLineTokens(0),cmEditor.getLineTokens(0));
				resEditor.getDoc().markText({line:0,ch:tokensRe.start},{line:0,ch:tokensRe.end},{css: "background-color: #d5fdd5"});

				// var t = cmEditor.getLineTokens(0)[2];
				// console.log(t)
				// //cmEditor.getDoc().markText({line:cmEditor.getLineTokens(0)[2].start,ch:cmEditor.getLineTokens(0)[2].end},{line:cmEditor.getLineTokens(0)[3].start,ch:cmEditor.getLineTokens(0)[3].end},{css: "background-color: red"});
				// cmEditor.getDoc().markText({line:0,ch:12},{line:0,ch:20},{css: "background-color: green"});

				// console.log(t.start)



			}else{
				setHasNext(false);
				// let c = getCurr();
				// let elem = allExpr[c];

				// cmEditor.setValue(elem.expr);
				// resEditor.setValue(elem.res);
				// resEditor.setValue("");
				$("#step").attr("disabled", true);
			}
			
			$("#stop").attr("disabled", false);
		},
		error : function(e) {
			console.log("ERROR: ", e);
			
		}
	});

	// current = allExpr.length-1;
	// setCurr(allExpr.length-1);
}

function getStartToken(source, result){
	var sLength = source.length;
	var rLength = result.length;

	var start = 0;
	var end = 0;

	var p1 = 0;
	var p2 = 0;

	while(p1 < sLength){
		console.log(source[p1].string + "==="+ result[p2].string)
		if(source[p1].string === result[p2].string){
			p1 += 1;
			p2 += 1;
		} else{
			start = source[p1].start;
			break;
		}
	}

	p1 = sLength-1;
	p2 = rLength-1;

	while(p1 > -1){
		console.log("2. " + source[p1].string + "==="+ result[p2].string)
		if(source[p1].string === result[p2].string){
			p1 -= 1;
			p2 -= 1;
		} else{
			end = source[p1].end;
			break;
		}
	}

	return {start: start, end: end};
}
function nextStep(cmEditor,resEditor,allExpr){
	var cursor = resEditor.getCursor();
	var cursor2 = cmEditor.getCursor();
	console.log(cursor);
	console.log(cursor2);
	// cursor2.line +=1;
	// cmEditor.setCursor(cursor2);
	// var expression = resEditor.getLine(cursor.line);
	// cmEditor.replaceRange('\n'+expression,cursor2);
	if(getCurr() === allExpr.length-1){
		if(!getHasNext()){
			$("#step").attr("disabled", true);
		}else{
			//var expression = resEditor.getLine(cursor.line);
			var expression = resEditor.getValue();
			// cmEditor.setValue(expression);
			run(expression,cmEditor,resEditor,allExpr,getCurr());	
		}		
	} else{
		let c = getCurr();
		setCurr(++c);
		console.log("current > 0 => " + getCurr());
		var elem = allExpr[c];
		cmEditor.setValue(elem.expr);
		resEditor.setValue(elem.res);
		$("#prev").attr("disabled", false);
	}
	
	
}

function prevStep(editableCodeMirror,readOnlyCodeMirror,allExpr){
	let c = getCurr();
	if(c>0){
		console.log(allExpr);
		setCurr(--c);
		console.log("current > 0 => " + getCurr());
		var elem = allExpr[c];
		editableCodeMirror.setValue(elem.expr);
		readOnlyCodeMirror.setValue(elem.res);
		$("#step").attr("disabled", false);

	}
	if(c===0){
		console.log("current <= 0 => " + c);
		$("#prev").attr("disabled", true);
	}
}