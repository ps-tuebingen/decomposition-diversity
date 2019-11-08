/**
 * 
 * @author Fayez Abu Alia
 */

$(document).ready(function(){

	var code = $(".form-control")[0];
	var editor = CodeMirror.fromTextArea(code,{
		autoCloseBrackets: true,
		lineNumbers : true,
		lineWrapping: true,
 	 	matchBrackets: true,
  		mode: 'uroboro',
  		styleActiveLine: true,
  		theme: 'uroboro',
  		extraKeys: {"Ctrl-Space": "autocomplete"},
  		highlightSelectionMatches: {showToken: /\w/, annotateScrollbar: true},
  		gutters: ["CodeMirror-lint-markers"],
  	    lint: true
	});
	$('.CodeMirror').on('mousemove', function(e) {
    //editor.on('mousemove', function(e) {
    	console.log("MOVE MOVE")
    	$('.preview').css({
		        'top' : e.pageY+7,
		        'left' : e.pageX-30
		  	});
		 
		});
		// Add Preview
	$('body').append('<div class="preview"></div>');
	
	/*var editor = CodeMirror.fromTextArea(document.getElementById('editor'),{
		lineNumbers : true
	});*/

	editor.on("mousedown", function(editor,e){
		$('.preview').css('visibility', 'hidden');
	});

	editor.on("contextmenu", function () { 
    	event.preventDefault();
    	 $('.preview').css('visibility', 'hidden');
    	//let word = editor.findWordAt(editor.getCursor());
    	//editor.setSelection(word.anchor, word.head);
    	let name = editor.getSelection();
    	let cur = editor.getCursor();
    	let token = editor.getTokenAt(cur);

    	var w = editor.findWordAt(cur);
    	var word = editor.getRange(w.anchor,w.head);
    	
    	var element = document.getElementById('sourceCode');
        
        switch(token.type){
        	case "variable":
        	case "typename":
        	case "cons":
        	case "local-cons":
        	case "destructor":
        	case "local-destructor":
        	case "match-comatch":
        		if(element.classList.contains('ctx-menu')){
	        		element.classList.remove('ctx-menu');	
	        	}

	        	if(!element.classList.contains('ctx-menu-ref')){
	        		element.classList.add('ctx-menu-ref');
	        	}
	        	
	        	showCtxMenuWithRefactoring('.ctx-menu-ref',editor);
        		break;
        	
        	default:
        		/*if(!element.classList.contains('ctx-menu')){
	        		element.classList.add('ctx-menu');	
	        	}

	        	if(element.classList.contains('ctx-menu-ref')){
	        		element.classList.remove('ctx-menu-ref');
	        	}
	        	showCtxMenu('.ctx-menu',editor);*/
        		break;
        	
        }

          
	}); 

	Notification.init({
        "selector": ".bb-alert"
    });
        
	
//	$('#errorMsg').hide();
	$("#refuncBtn").click(function(event){
		// Prevent the form from submitting via the browser.
		event.preventDefault();
        if (editor.getValue() === '') {
        	var element = document.getElementById('runResult');
			element.classList.add('error');
			$('#runResult').val('Please enter your code!');
        } else {
    		refunc(editor);
        }
		
	});
	
	$("#defuncBtn").click(function(event){
		// Prevent the form from submitting via the browser.
		event.preventDefault();
		if (editor.getValue() === '') {
        	var element = document.getElementById('runResult');
			element.classList.add('error');
			$('#runResult').val('Please enter your code!');
        } else {
        	defunc(editor);
        }
	});
	
	$("#parseBtn").click(function(event){
		// Prevent the form from submitting via the browser.
		event.preventDefault();
		if (editor.getValue() === '') {
        	var element = document.getElementById('runResult');
			element.classList.add('error');
			$('#runResult').val('Please enter your code!');
        } else {
        	parseProg(editor);
        }
	});
	
	 $("#stepp").click(function(event){
        var host = window.location.hostname
        var port = window.location.port
	    var stepperWin = window.open("http://" + host + ":" + port + "/decompositiondiversity/stepper","_blank");
	    
	 // Prevent the form from submitting via the browser.
		event.preventDefault();
	});
	 
	$("#setConf").click(function(event){
		// Prevent the form from submitting via the browser.
		event.preventDefault();
		setConfig();
	});
	
	editor.on('keyup', function(editor,event){
		if (!editor.state.completionActive &&   /*Enables keyboard navigation in autocomplete list*/
     			event.keyCode > 64 && event.keyCode < 91){

    		CodeMirror.commands.autocomplete(editor, null, {completeSingle: false});

		}

		// var cmLines = document.querySelectorAll('.CodeMirror-line');
		// for (var cml of cmLines) {
		// 	console.log(cml);

		// 	cml.addEventListener('mouseenter', function (e) {
		// 	    console.log(this.textContent)
		// 		$('.preview').css('visibility', 'visible');
		// 		$('.preview').empty().html('<p> HIEER <\p>');
		// 	}, false);
		// }
	});

	var info = {line : -1, type : ""};
	editor.on("change", function(){
		if(editor.getValue() != ''){
			$("#save").attr("disabled", false);
			$("#trash").attr("disabled", false);
			let cur = editor.getCursor();
			let token = editor.getTokenAt(cur);
			console.log(info)
			if(token.string === "consumer" || token.string === "generator" || 
				token.string === "match" || token.string === "comatch"){
				info = {line : cur.line,
						startCol: token.start,
						type : token.string};
			}

			if(info.line > -1){
				info = completeFun(editor,token,cur,info);
			}
			console.log(info)
			
			
		} else {
			$("#save").attr("disabled", true);
			$("#trash").attr("disabled", true);
		}
			
			
	});
	
	$("#addCons").click(function(event){
		event.preventDefault();
		/*let cursor = editor.getCursor();
		let line = editor.getLine(cursor.line);
		let arr = line.split(/[\s,\[\]]+/);

		let i = 0;
		let name = arr[i];
		while(i<arr.length && name ===""){
			++i;
			name = arr[i];
		}*/
		// let typename = getTypeName(editor,"cons");
		let data = localStorage.getItem("data");
		if(data===""){
			bootbox.alert({
				    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+"There are no declared data types" ,
				    callback: function () {
				        console.log('This was logged in the callback!');
				    }
				})
		} else {
			let params = {type: "constructor", op: "add", types:data};
			showBox(editor,params);
		}		
		// else {
		// 	//let name = editor.getSelection();

		// 	let cur = editor.getCursor();
	 //    	let token = editor.getTokenAt(cur);

	 //    	var w = editor.findWordAt(cur);
	 //    	var name = editor.getRange(w.anchor,w.head);

		// 	getAllCases(name,typename,editor,"constructor",false);
		// }
		
	});

	$("#addParamsCons").click(function(event){
		event.preventDefault();
		// TODO: add typename
		let name = editor.getSelection();

		let typename = getTypeName(editor,"cons");
		getAllCases(name,typename,editor,"constructor",true);
	});

	$("#addParamsDes").click(function(event){
		event.preventDefault();
		// TODO: add typename
		let name = editor.getSelection();

		let typename = getTypeName(editor,"destructor");

		getAllCases(name,typename,editor,"destructor",true);
	});

	$("#removeCons").click(function(event){
		event.preventDefault();
		let data = localStorage.getItem("data");
		if(data===""){
			bootbox.alert({
				    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+"There are no declared constructors" ,
				    callback: function () {
				        console.log('This was logged in the callback!');
				    }
				})
		} else {
			let params = {type: "constructor", op: "remove", types:data};
			showBoxremove(editor,params);
		}
		// let typename = getTypeName(editor,"cons");

		// if(typename === null){
		// 	bootbox.alert({
		// 		    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+"Datatype did not found" ,
		// 		    callback: function () {
		// 		        console.log('This was logged in the callback!');
		// 		    }
		// 		})
		// } else {
		// 	let name = editor.getSelection();
		// 	removeConsOrDes(name,typename,editor,"constructor");
		// }
	});

	$("#removeDes").click(function(event){
		event.preventDefault();
		
		let codata = localStorage.getItem("codata");
		if(codata===""){
			bootbox.alert({
				    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+"There are no declared destructors" ,
				    callback: function () {
				        console.log('This was logged in the callback!');
				    }
				})
		} else {
			let params = {type: "destructor", op: "remove", types:codata};
			showBoxremove(editor,params);
		}
		// let typename = getTypeName(editor,"destructor");

		// if(typename === null){
		// 	bootbox.alert({
		// 		    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+"Datatype did not found" ,
		// 		    callback: function () {
		// 		        console.log('This was logged in the callback!');
		// 		    }
		// 		})
		// } else {
		// 	let name = editor.getSelection();
		// 	removeConsOrDes(name,typename,editor,"destructor");
		// }
	});

	$("#addDes").click(function(event){
		event.preventDefault();
		/*let cursor = editor.getCursor();
		let line = editor.getLine(cursor.line);
		let arr = line.split(/[\s,\[\]]+/);

		let i = 0;
		let name = arr[i];
		while(i<arr.length && name ===""){
			++i;
			name = arr[i];
		}*/
		let codata = localStorage.getItem("codata");
		if(codata===""){
			bootbox.alert({
				    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+"There are no declared codata types" ,
				    callback: function () {
				        console.log('This was logged in the callback!');
				    }
				})
		} else {
			let params = {type: "destructor", op: "add", types:codata};
			showBox(editor,params);
		}
		// let typename = getTypeName(editor,"destructor");

		// if(typename === null){
		// 	bootbox.alert({
		// 		    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+"Datatype did not found" ,
		// 		    callback: function () {
		// 		        console.log('This was logged in the callback!');
		// 		    }
		// 		})
		// } else {
		// 	let name = editor.getSelection();
		// 	getAllCases(name,typename,editor,"destructor",false);
		// }
	});

	$("#extractMatch").click(function(event){
		event.preventDefault();

		let name = editor.getSelection();
		extract(name,editor,"match");
	});

	$("#extractCMatch").click(function(event){
		event.preventDefault();

		let name = editor.getSelection();
		extract(name,editor,"comatch");
	});

	$("#inline").click(function(event){
		event.preventDefault();

		let name = editor.getSelection();
		inline(name,editor);
	});
	$("#formatBtn").click(function(event){
		event.preventDefault();

		$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/format",
		
		dataType : 'json',
		success : function(result) {
			if(result.status === "success"){
				editor.setValue(result.data);
			} else{
				editor.setValue(editor.getValue());
			}
			$('#runResult').val(result.data);
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val(JSON.stringify(e));		
		}
	});
	});

	$("#save").click(function(event){
		// Prevent the form from submitting via the browser.
		event.preventDefault();
		bootbox.prompt("Save program as:", 
				function(result){ 
					console.log(result);
					if(result!==null){
						saveFile(result, editor);
						$("#save").attr("disabled", true);
					}
					
				});
	});
	
	$("#upload").on("change",function(event){
		// Prevent the form from submitting via the browser.
		event.preventDefault();
		console.log("clicked");
		console.log(event);
		var file = event.target.files[0];
		console.log("file");
		  if (file) {
			  console.log("file = true");
		      var reader = new FileReader();
		      reader.readAsText(file, "UTF-8");
		      reader.onload = function (event) {
		    	  editor.setValue(event.target.result);
		      }
		      reader.onerror = function (event) {
		          console.log("error reading file");
		      }
		  }
		
	});
	
	$("#trash").click(function(event){
		// Prevent the form from submitting via the browser.
		event.preventDefault();
		editor.setValue('');
		removeErrorClass();
		$('#runResult').val('');
		$("#save").attr("disabled", true);
		$("#trash").attr("disabled", true);
	});
	
	$('[data-toggle="tooltip"]').click(function () {
        $('[data-toggle="tooltip"]').tooltip("hide");

    });

});

function showBox(editor,params){
	// let type = params.type.charAt(0).toUpperCase() + params.type.slice(1);
	let t = params.type.charAt(0).toUpperCase() + params.type.slice(1);
	let placeholder = "";
	if(params.type === "constructor"){
	    placeholder += "Name";
		placeholder += "(Type1,Type2,...)";
	} else {
	    placeholder += "name";
		placeholder += "(T1,T2,...):RT";
	}
	let o = params.op.charAt(0).toUpperCase() + params.op.slice(1);
	let tt = params.types.split(",");

	let form = "<form id='infos' action=''>";
	form += "<div class='form-group row'>";
	form += "<label for='inputType' class='col-sm-2 col-form-label'>Type</label>";
	form += "<div id='divType' class='col-sm-10'>";
	form += "<select id='inputType' class='form-control' required>";
	form += "<option selected>Choose...</option>";
	for(var i = 0; i<tt.length;++i){
		form += "<option>"+tt[i]+"</option>"; 
	}
	form += "</select>";
	form += "</div>";
	form += "</div>";
	//
	form += "<div class='form-group row'>";
	form += "<label for='inputName' class='col-sm-2 col-form-label'>Signature</label>";
	form += "<div id='divName' class='col-sm-10'>";
	form += "<input type='text' class='form-control' id='inputName' placeholder='"+placeholder+"' required>";
	form += "</div>";
	form += "</div>";
	
	form += "</form>";
	
	var $dialog = bootbox.confirm({
	    title: o + " " + t,
	    message: form,
	    onEscape: true,
	    buttons: {
	       confirm: {
	            label: o + " " + t,
	            className: 'btn-confirm'
	        },
	        cancel: {
	            label: 'Cancel',
	            className: 'btn-grey'
	        }
	    },
	    callback: function (result) {
	    	if(result){
	    		let valid = checkAddForm(params.type);
	    		let elem = document.getElementById('inputType');
	    		let element = document.getElementById('inputName');
	    		if(valid){
	    			if(elem.classList.contains("error")){
				          elem.classList.remove("error");
				          if (document.getElementById('spanType')) {
							var parent = document.getElementById('divType'); 
					    	var child = document.getElementById('spanType');
					    	parent.removeChild(child);
						  }
				     }
				     if(element.classList.contains("error")){
				     	element.classList.remove("error");
				     	if (document.getElementById('spanName')) {
							var parent = document.getElementById('divName'); 
					    	var child = document.getElementById('spanName');
					    	parent.removeChild(child);
						  }
				     }
		    		let sig = element.value.replace(/\s+/, "");
			    	let typename = elem.value;

			    	let req = {signature: sig, typename: typename, type: params.type, addParams: false};
			  		getBody(editor,req);
			  	}else{
			  		
			  		if(elem.value === "Choose..."){
						elem.classList.add('error');
						addSpanToDiv(document.getElementById('divType'),'Type required', 'spanType');
					} else {
						if(elem.classList.contains("error")){
				            elem.classList.remove("error");
				          }
				          if (document.getElementById('spanType')) {
							var parent = document.getElementById('divType'); 
					    	var child = document.getElementById('spanType');
					    	parent.removeChild(child);
						  }
					}
			  		
			  		element.classList.add('error');
			  		addSpanToDiv(document.getElementById('divName'),'Signature is invalid','spanName');
			  		return false;
			  	}
	    	}
	    }
	});

	$dialog.on('shown.bs.modal', function(e){
	    var $form = $('#infos');

	    $form.on('submit', function(fe){
	        fe.preventDefault();

	        $dialog.find('.btn-confirm').trigger('click');
	    });
	});
}

function addSpanToDiv(div,msg,id){
	if(!document.getElementById(id)){
		var newSpan = document.createElement('span');
		newSpan.innerHTML = msg;
		newSpan.setAttribute("id", id);
		newSpan.classList.add('span-error');
		div.appendChild(newSpan);
	}
}

function checkAddForm(type){
	var form = $('#infos');
	var sig = document.getElementById('inputName').value;
	var typename = document.getElementById('inputType').value;

	if(sig ==="" || typename === "Choose..."){
		return false;
	}
	var syntax;
	if(type==="constructor"){
		syntax = /\_?[A-Z][a-zA-Z0-9]*\s*\(\s*(\w+(,\s*\w+)*)?\s*\)\s*/;
	}else {
		syntax = /\_?[a-z][a-zA-Z0-9]*\s*\(\s*(\w+(,\s*\w+)*)?\s*\)\s*\:\s*[A-Z][a-zA-Z0-9]*\s*/;
	}
	if(syntax.test(sig)){
		var data = localStorage.getItem("data");
		var codata = localStorage.getItem("codata");

		var darr = data.split(",");
		var cdarr = codata.split(",");

        var sigSub = sig.match(/\(([^\)]*)\)/)[1]
		var arr = sigSub.split(/[\s,\[\]_]+/);

		var index = arr[0]===""?2:1;
		for(var i = index; i<arr.length-1; ++i){
			if(!arrContains(darr,arr[i]) && !arrContains(cdarr,arr[i]))
				return false;
		}

	} else {
		return false;
	}

	return true;
}

function showBoxremove(editor,params){
	// let type = params.type.charAt(0).toUpperCase() + params.type.slice(1);
	let t = params.type.charAt(0).toUpperCase() + params.type.slice(1);
	
	let o = params.op.charAt(0).toUpperCase() + params.op.slice(1);
	let tt = params.types.split(",");

	let form = "<form id='removeForm' action='javascript:getNames()' method='POST'>";
	form += "<div class='form-group row'>";
	form += "<label for='inputType' class='col-sm-2 col-form-label'>Type</label>";
	form += "<div id='divType' class='col-sm-10'>";
	form += "<select id='inputType' class='form-control' onchange='this.form.submit()'>";
	form += "<option selected>Choose type ...</option>";
	for(var i = 0; i<tt.length;++i){
		form += "<option>"+tt[i]+"</option>"; 
	}
	form += "</select>";
	form += "</div>";
	form += "</div>";
	//
	
	
	form += "</form>";
	
	var $dialog = bootbox.confirm({
	    title: o + " " + t,
	    message: form,
	    onEscape: true,
	    buttons: {
	       confirm: {
	            label: o + " " + t,
	            className: 'btn-confirm'
	        },
	        cancel: {
	            label: 'Cancel',
	            className: 'btn-grey'
	        }
	    },
	    callback: function (result) {
	    	if(result){
	    		
	    		if(document.getElementById('inputName')){
	    			let name = document.getElementById('inputName').value;
		    		let typename = document.getElementById('inputType').value;
		    		if(name === "Choose name ..."){
		    			let elem = document.getElementById('inputName');
		    			elem.classList.add('error');
		    			addSpanToDiv(document.getElementById('divName'),'Name required', 'spanName');
		    			return false;
		    		}else{
		    			if (document.getElementById('spanName')) {
							var parent = document.getElementById('divName'); 
					    	var child = document.getElementById('spanName');
					    	parent.removeChild(child);
						}
		    			removeConsOrDes(name,typename,editor,params.type)
		    		}
	    		} else{
	    			return false;
	    		}
	    	}
	    }
	});

	$dialog.on('shown.bs.modal', function(e){
	    var $form = $('#removeForm');

	    $form.on('submit', function(fe){
	        fe.preventDefault();

	        $dialog.find('.btn-confirm').trigger('click');
	    });
	});
}

function getNames(){
	var elem = document.getElementById('inputType');
	if(elem.value !== "Choose type ..."){
		if (document.getElementById('spanType')) {
			var parent = document.getElementById('divType'); 
    		var child = document.getElementById('spanType');
    		parent.removeChild(child);
	    }
	    
	    if(elem.classList.contains("error")){
        	elem.classList.remove("error");
      	}

		let form = $("#removeForm");
		if (document.getElementById('nameList')) {
			var parent = document.getElementById('removeForm'); 
	    	var child = document.getElementById('nameList');
	    	parent.removeChild(child);
		}
		let tn = elem.value;
		let params = {typename:tn};

		let toAdd = "<div class='form-group row' id='nameList'>";
		toAdd += "<label for='inputName' class='col-sm-2 col-form-label'>Name</label>";
		toAdd += "<div id='divName' class='col-sm-10'>";
		toAdd += "<select id='inputName' class='form-control'>";
		toAdd += "<option selected>Choose name ...</option>";
		
			
		
		toAdd += "</select>";
		toAdd += "</div>";
		toAdd += "</div>";
		$(form).append(toAdd);
		$.ajax({
			type : "POST",
			contentType : "application/json",
			url : "api/getConsOrDesList",
			data : JSON.stringify(params),
			dataType : 'json',
			success : function(result) {
				if(result.status === "success"){
					var select = document.getElementById('inputName');
					let options = JSON.parse(result.data);
					if(options.length>0){
						for(var i = 0;i<options.length;++i){
							var opt = document.createElement('option');
					    	opt.value = options[i];
					    	opt.innerHTML = options[i];
					    	select.appendChild(opt);
						}	
					} else{
						var parent = document.getElementById('removeForm'); 
	    				var child = document.getElementById('nameList');
	    				parent.removeChild(child);
						bootbox.alert({
					    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> There are no declared constructors/destructors' ,
					    callback: function () {
					        console.log('This was logged in the callback!');
					    }
					})
					}
					
				} else{
					bootbox.alert({
					    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+result.data ,
					    callback: function () {
					        console.log('This was logged in the callback!');
					    }
					})
					
				}
			},
			error : function(e) {
				console.log("ERROR: ", e);
				$('#runResult').val(JSON.stringify(e));		
			}
		});

			
	} else {
		let elem = document.getElementById('inputType');
	    elem.classList.add('error');
		addSpanToDiv(document.getElementById('divType'),'Type required', 'spanType');
		if (document.getElementById('nameList')) {
			var parent = document.getElementById('removeForm'); 
	    	var child = document.getElementById('nameList');
	    	parent.removeChild(child);
		}
	}
	
}

function removeConsOrDes(name,typename,editor,type){
	var params = {name:name, typename:typename, type:type};

	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/removeConsOrDes",
		data : JSON.stringify(params),
		dataType : 'json',
		success : function(result) {
			if(result.status === "success"){
				editor.setValue(result.data);
			} else{
				bootbox.alert({
				    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+result.data ,
				    callback: function () {
				        console.log('This was logged in the callback!');
				    }
				})
				
				editor.setValue(editor.getValue());
			}
			$('#runResult').val(result.data);
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val(JSON.stringify(e));		
		}
	});
}

function getTypeName(editor,consOrDes) {
	// consOrDes = "cons" OR "destructor"
	let cursor = editor.getCursor();
	let l = cursor.line;
	
	let token = editor.getTokenAt(cursor);
	
	let typename = null;

	if(token.type === consOrDes){
		let toFind;
		if(consOrDes === "cons"){
			toFind = "data";
		} else {
			toFind = "codata";
		}

		let found = false;
		
		while(!found && l >= 0){
			let line = editor.getLine(l);
			let arr = line.split(/[\s,\[\]]+/);
			let index = -1;
			for(let i = 0;i<arr.length;++i){
				if(arr[i] === toFind){
					found = true;
					index = i;
					break;
				}
			}
			if(!found){
				--l;
			} else {
				typename = arr[++index];
			}
		}
		
	}

	return typename;
}

function showCtxMenuWithRefactoring(className,editor){
	$.contextMenu({
            selector: className,
            build: function($trigger, e) { 
            	return {
            		callback: function(key, options) {
		                var m = "clicked: " + key;
		                console.log(options);
		                var cur = editor.getCursor();
						var w = editor.findWordAt(cur);
						var word = editor.getRange(w.anchor,w.head);
						var typename;
		                switch(key){
		                	/*case "cut":
		                		var selection = editor.getSelection(" ");
								if(selection === ""){
									toCut = word;
									editor.setSelection(w.anchor,w.head);
									console.log(cur)
									
								}
								
		                		document.addEventListener('cut', function (ev) {
								    ev.clipboardData.setData('text/plain', toCut);
								    var from = {line: cur.line, ch: w.anchor};
									var to = {line: cur.line, ch: w.head};
									editor.replaceRange("",from,to);
								    ev.preventDefault();
								});
								
								// document.execCommand('cut');
								
								// editor.replaceRange("",cur);
								
		                		break;
		                	case "copy":
		                		var selection = editor.getSelection(" ");
								var toCopy = (selection === "")?word:selection;

		                		document.addEventListener('copy', function (ev) {
								    ev.clipboardData.setData('text/plain', toCopy);
								    ev.preventDefault();
								});
								//document.execCommand('copy');
		                		break;
		                	case "paste":
		                		//var toPaste="";
		                		document.addEventListener('paste', function (ev) {
								    //toPaste = ev.clipboardData.getData("text");
								    ev.preventDefault();

								    var clipboardData, pastedData;
		                			// Get pasted data via clipboard API
		    						clipboardData = ev.clipboardData || window.clipboardData;
		    						pastedData = clipboardData.getData('Text');
									var from = {line: cur.line, ch: w.anchor};
									var to = {line: cur.line, ch: w.head};
									editor.replaceRange(pastedData,from,to);
		    						console.log(pastedData)
		    						console.log(pastedData)
		    						alert(pastedData);
								});
								//document.execCommand('paste');
								
								//editor.replaceRange(toPaste,cur);
								
		                		break;
		                	case "delete":
		                		break;*/
		                	case "rename":
		                		CodeMirror.commands.replaceAll(editor);
		                		break;
		                	case "addCons":
		                		typename = getTypeName(editor,"cons");
		                		getAllCases(word,typename,editor,"constructor",false);
		                		break;
		                	case "addDes":
		                		typename = getTypeName(editor,"destructor");
		                		getAllCases(word,typename,editor,"destructor",false);
		                		break;
		                	
		                	case "removeCons":
		                		typename = getTypeName(editor,"cons");
		                		removeConsOrDes(word,typename,editor,"constructor");
		                		break;
		                	case "removeDes":
		                		typename = getTypeName(editor,"destructor");
		                		removeConsOrDes(word,typename,editor,"destructor");
		                		break;
		                	case "addRemoveParamCons":
		                		typename = getTypeName(editor,"cons");
		                		getAllCases(word,typename,editor,"constructor",true);
		                		break;
		                	case "addRemoveParamDes":
		                		typename = getTypeName(editor,"destructor");
		                		getAllCases(word,typename,editor,"destructor",true);
		                		break;
		                	case "inline":
		                		inline(word,editor);
		                		break;
		                	case "extractMatchFun":
		                		extract(word,editor,"match");
		                		break;
		                	case "extractCoMatchFun":
		                		extract(word,editor,"comatch");
		                		break;
		                	default:
		                		break;
		                }
		                //window.console && console.log(m) || alert(m);

		            },
	            items: {
	                /*"cut": {name: "Cut", icon: "cut"},
	               copy: {name: "Copy", icon: "copy"},
	                "paste": {name: "Paste", icon: "paste"},
	                "delete": {name: "Delete", icon: "delete"/*, disabled: function(key, opt){        
				            // Disable this item if the menu was triggered on a div
				            if(token.type === "variable" || token.type === "variable-2" || token.type === "variable-3"){
				                return true;
				            }            
				        }*/
				    /*},
				    "sep" : "---------",*/
				    "source" :{"name":"Source",
				    			"items":{
				    				"addCons": {
	        									"name": "Add constructor", 
	        									
	        									},
    								"addDes": {
    									"name": "Add destructor", 
    									
    									},
    								"sep2" : "---------",
    								"removeCons": {
    									"name": "Remove constructor", 
    									
    									},
    								"removeDes": {
    									"name": "Remove destructor", 
    									
    									}
				    			}
							},
	        		}
	        	};
        	}
        });
}

function showCtxMenu(className,word){
	$.contextMenu({
            selector: className, 
            callback: function(key, options) {
                var m = "clicked: " + key;
                console.log(options);
                window.console && console.log(m) || alert(m);

            },
            items: {
                "cut": {name: "Cut", icon: "cut"},
               copy: {name: "Copy", icon: "copy"},
                "paste": {name: "Paste", icon: "paste"},
                "delete": {name: "Delete", icon: "delete"/*, disabled: function(key, opt){        
			            // Disable this item if the menu was triggered on a div
			            if(token.type === "variable" || token.type === "variable-2" || token.type === "variable-3"){
			                return true;
			            }            
			        }*/
			    }
			}
        });
}

function inline(name,editor) {
	var params = {name:name, source:""};

	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/inline",
		data : JSON.stringify(params),
		dataType : 'json',
		success : function(result) {
			if(result.status === "success"){
				editor.setValue(result.data);
			} else{
				bootbox.alert({
				    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+result.data ,
				    callback: function () {
				        console.log('This was logged in the callback!');
				    }
				})
				
				editor.setValue(editor.getValue());
			}
			$('#runResult').val(result.data);
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val(JSON.stringify(e));		
		}
	});
}

function extract(name,editor,type){
	var params = {name:name, type:type, source:""};

	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/extractFun",
		data : JSON.stringify(params),
		dataType : 'json',
		success : function(result) {
			if(result.status === "success"){
				editor.setValue(result.data);
			} else{
				bootbox.alert({
				    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+result.data ,
				    callback: function () {
				        console.log('This was logged in the callback!');
				    }
				})

				editor.setValue(editor.getValue());
			}
			$('#runResult').val(result.data);
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val(JSON.stringify(e));		
		}
	});
}

function getBody(editor,params){
	
	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/getBody",
		data : JSON.stringify(params),
		dataType : 'json',
		success : function(result) {
			if(result.status == "success"){
				//let data = JSON.parse(result.data);
				console.log(result.data)
				let data = result.data;

				let body = data.body;

				let title = "Complete ";
				if(params.type === "constructor"){
					title += "the generator function"
				} else{
					title += "the consumer function"
				}

				var diaCM;
				var win = bootbox.prompt({
						    title: title,
						    inputType: 'textarea',
						    onEscape: true,
						    callback: function (result) {
						        console.log(diaCM.getValue())
						        if(result != null){
						        	if(params.addParams){
						        		addParameters(editor,diaCM.getValue(),params.type,params.signature);
						        	}else{
						        		addNewConsOrDes(editor,diaCM.getValue(),params.type,params.signature);	
						        	}
						        } else {
						        	editor.setValue(editor.getValue());
						        }
						    }
						});
				win.on("shown.bs.modal", function() {
					console.log(win)
					console.log($('.modal-body'))
				    diaCM = CodeMirror.fromTextArea($(".bootbox-input-textarea")[0], {
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
			    	$('.modal-body').on('mousemove', function(e) {
				    //editor.on('mousemove', function(e) {
				    	console.log("MOVE MOVE")
				    	$('.preview').css({
						        'top' : e.pageY,
						        'left' : e.pageX
						      });
					});
			    	
			    	diaCM.on('keyup', function(event){

						var selector = document.querySelector('.modal-body');
						var cmLines = selector.querySelectorAll('.CodeMirror-line');
						for (var cml of cmLines) {
							console.log(cml);
							var dest = cml.querySelectorAll('.cm-destructor');
					        var cons = cml.querySelectorAll('.cm-cons');
					        var lDest = cml.querySelectorAll('.cm-local-destructor');
					        var lCons = cml.querySelectorAll('.cm-local-cons');
					        for(var d of dest){
					          d.addEventListener('mouseenter', function (e) {
					            console.log(this.textContent)
					            var name = this.textContent;
					            console.log(result.data.consAndDesMap[name])
					            if(result.data.consAndDesMap[name] == undefined){
					              $('.preview').css('visibility', 'hidden');
					              $('.preview').css('z-index', '2');
					            }else {
					              $('.preview').css('visibility', 'visible');
					              $('.preview').css('z-index', '9999');
					              $('.preview').empty().html(result.data.consAndDesMap[name]); 
					            }
					            
					          }, false); 

					          d.addEventListener('mouseleave', function (e) {
					            //console.log(this.textContent)
					            $('.preview').css('visibility', 'hidden');
					            $('.preview').css('z-index', '2');
					          }, false); 
					        }

					        for(var d of lDest){
					          d.addEventListener('mouseenter', function (e) {
					            console.log(this.textContent)
					            var name = this.textContent;
					            console.log(result.data.consAndDesMap[name])
					            if(result.data.consAndDesMap[name] == undefined){
					              $('.preview').css('visibility', 'hidden');
					              $('.preview').css('z-index', '2');
					            }else {
					              $('.preview').css('visibility', 'visible');
					              $('.preview').css('z-index', '9999');
					              $('.preview').empty().html(result.data.consAndDesMap[name]); 
					            }
					            
					          }, false); 

					          d.addEventListener('mouseleave', function (e) {
					            //console.log(this.textContent)
					            $('.preview').css('visibility', 'hidden');
					            $('.preview').css('z-index', '2');
					            
					          }, false); 
					        }

					        for(var c of cons){
					          c.addEventListener('mouseenter', function (e) {
					            console.log(this.textContent)
					            var name = this.textContent;
					            if(result.data.consAndDesMap[name] == undefined){
					              $('.preview').css('visibility', 'hidden');
					              $('.preview').css('z-index', '2');
					            } else {
					              $('.preview').css('visibility', 'visible');
					              $('.preview').css('z-index', '9999');
					              $('.preview').empty().html(result.data.consAndDesMap[name]);  
					            }
					           
					          }, false); 

					          c.addEventListener('mouseleave', function (e) {
					            //console.log(this.textContent)
					            $('.preview').css('visibility', 'hidden');
					            $('.preview').css('z-index', '2');
					            
					          }, false); 
					        }

					        for(var c of lCons){
					          c.addEventListener('mouseenter', function (e) {
					            console.log(this.textContent)
					            var name = this.textContent;
					            if(result.data.consAndDesMap[name] == undefined){
					              $('.preview').css('visibility', 'hidden');
					              $('.preview').css('z-index', '2');
					            } else {
					              $('.preview').css('visibility', 'visible');
					              $('.preview').css('z-index', '9999');
					              $('.preview').empty().html(result.data.consAndDesMap[name]);  
					            }
					           
					          }, false); 

					          c.addEventListener('mouseleave', function (e) {
					            //console.log(this.textContent)
					            $('.preview').css('visibility', 'hidden');
					            $('.preview').css('z-index', '2');
					            
					          }, false); 
					        }
						}
					});

					
					
			    	diaCM.setValue(body);
			    	
			    	diaCM.setCursor({line:diaCM.lastLine(),ch:0})
					diaCM.setSelection(diaCM.getCursor());
					diaCM.doc.replaceSelections([" "]);
					CodeMirror.signal(diaCM, "change",{from:{line:diaCM.lastLine,ch:0},to:{line:diaCM.lastLine,ch:1},text:[" "],removed:""});
			    	
					var selector = document.querySelector('.modal-body');
					var cmLines = selector.querySelectorAll('.CodeMirror-line');
					for (var cml of cmLines) {
						console.log(cml);
						var dest = cml.querySelectorAll('.cm-destructor');
				        var cons = cml.querySelectorAll('.cm-cons');
				        var lDest = cml.querySelectorAll('.cm-local-destructor');
				        var lCons = cml.querySelectorAll('.cm-local-cons');
				        for(var d of dest){
				          d.addEventListener('mouseenter', function (e) {
				            console.log(this.textContent)
				            var name = this.textContent;
				            console.log(result.data.consAndDesMap[name])
				            if(result.data.consAndDesMap[name] == undefined){
				              $('.preview').css('visibility', 'hidden');
				              $('.preview').css('z-index', '2');
				            }else {
				              $('.preview').css('visibility', 'visible');
				              $('.preview').css('z-index', '9999');
				              $('.preview').empty().html(result.data.consAndDesMap[name]); 
				            }
				            
				          }, false); 

				          d.addEventListener('mouseleave', function (e) {
				            //console.log(this.textContent)
				            $('.preview').css('visibility', 'hidden');
				            $('.preview').css('z-index', '2');
				          }, false); 
				        }

				        for(var d of lDest){
				          d.addEventListener('mouseenter', function (e) {
				            console.log(this.textContent)
				            var name = this.textContent;
				            console.log(result.data.consAndDesMap[name])
				            if(result.data.consAndDesMap[name] == undefined){
				              $('.preview').css('visibility', 'hidden');
				              $('.preview').css('z-index', '2');
				            }else {
				              $('.preview').css('visibility', 'visible');
				              $('.preview').css('z-index', '9999');
				              $('.preview').empty().html(result.data.consAndDesMap[name]); 
				            }
				            
				          }, false); 

				          d.addEventListener('mouseleave', function (e) {
				            //console.log(this.textContent)
				            $('.preview').css('visibility', 'hidden');
				            $('.preview').css('z-index', '2');
				            
				          }, false); 
				        }

				        for(var c of cons){
				          c.addEventListener('mouseenter', function (e) {
				            console.log(this.textContent)
				            var name = this.textContent;
				            if(result.data.consAndDesMap[name] == undefined){
				              $('.preview').css('visibility', 'hidden');
				              $('.preview').css('z-index', '2');
				            } else {
				              $('.preview').css('visibility', 'visible');
				              $('.preview').css('z-index', '9999');
				              $('.preview').empty().html(result.data.consAndDesMap[name]);  
				            }
				           
				          }, false); 

				          c.addEventListener('mouseleave', function (e) {
				            //console.log(this.textContent)
				            $('.preview').css('visibility', 'hidden');
				            $('.preview').css('z-index', '2');
				            
				          }, false); 
				        }

				        for(var c of lCons){
				          c.addEventListener('mouseenter', function (e) {
				            console.log(this.textContent)
				            var name = this.textContent;
				            if(result.data.consAndDesMap[name] == undefined){
				              $('.preview').css('visibility', 'hidden');
				              $('.preview').css('z-index', '2');
				            } else {
				              $('.preview').css('visibility', 'visible');
				              $('.preview').css('z-index', '9999');
				              $('.preview').empty().html(result.data.consAndDesMap[name]);  
				            }
				           
				          }, false); 

				          c.addEventListener('mouseleave', function (e) {
				            //console.log(this.textContent)
				            $('.preview').css('visibility', 'hidden');
				            $('.preview').css('z-index', '2');
				            
				          }, false); 
				        }
					}

				});

				win.modal("show");
				$('.preview').css('z-index', '2');
				$('.preview').css('visibility', 'hidden');
				
			} else {
				bootbox.alert({
				    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+result.data.error ,
				    callback: function () {
				        console.log('This was logged in the callback!');
				    }
				})

				editor.setValue(editor.getValue());
			}
			$('#runResult').val(result.data);
			
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val(JSON.stringify(e));		
		}
	});
}




function getAllCases(name,typename,editor,type,addParams){
	var params = {name: name, typename: typename, type: type, addParams:addParams};
	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/getCases",
		data : JSON.stringify(params),
		dataType : 'json',
		success : function(result) {
			if(result.status == "success"){
				//let data = JSON.parse(result.data);
				console.log(result.data)
				let data = result.data;
				//let res = data.result;
				//let sig = data.signature;
				
				//window.program = JSON.parse(data.program);

				let body = data.body;


				// let form = "<form id='infos' action=''>";
				// form += "<div class='row'><div class='col'><textarea id='dialogEd'></textarea></div>";
				// for(var i = 0; i<names.length;++i){
				// 	form += "<div class='row'><div class='col'><p class='case-label' >"+names[i] + " => </p></div>"
				// 	+"<div class='col'><input type='text' id='case_"+i+"' class='case-input'/></div></div>"; 
				// }

				// form += "</form>";
				
				// bootbox.confirm({
				//     title: "Complete ... " + sig,
				//     message: form,
				//     buttons: {
				//        confirm: {
				//             label: 'OK',
				//             className: 'btn-success'
				//         },
				//         cancel: {
				//             label: 'Cancel',
				//             className: 'btn-danger'
				//         }
				//     },
				//     callback: function (result) {
				//     	if(result != null){
				// 	    	let exp = [];
				// 	    	for(var i = 0; i<names.length;++i){
				// 				let e = document.getElementById('case_'+i).value;
				// 				let cc = names[i] + " => " + e;
				// 				exp.push(cc);
				// 			}
				// 			addNewConsOrDes(editor,exp,type,name);
				// 			console.log('This was logged in the callback: ' + exp);
				// 		}
				        
				//     }
				// });

				/*
				let form = "<form id='infos' action=''>";
				form += "<div class='row'><div class='col'><textarea id='dialogEd'></textarea></div></div><div class='row'><div class='col'> <textarea id='funArea'></textarea></div></div>";
				form += "</form>";
				
				var win = bootbox.confirm({
					title: "Complete ... ",
				     message: form,
				     buttons: {
				        confirm: {
				             label: 'OK',
				             className: 'btn-success'
				         },
				         cancel: {
				             label: 'Cancel',
				             className: 'btn-danger'
				         }
				     },
				     callback: function (result) {
				     	}
				 });
				var diaCM;
				var diaCM2;
	
				win.on("shown.bs.modal", function() {
					console.log(win)
					console.log($('.modal-body'))
				    diaCM = CodeMirror.fromTextArea(document.getElementById('funArea'), {
				    	autoCloseBrackets: true,
						lineNumbers : true,
						lineWrapping: true,
				 	 	matchBrackets: true,
				  		mode: 'uroboro',
				  		styleActiveLine: true,
				  		theme: 'uroboro',
				  		extraKeys: {"Ctrl-Space": "autocomplete"},
				  		highlightSelectionMatches: {showToken: /\w/, annotateScrollbar: true},
				  		readOnly: true
			    	});
			    	diaCM2 = CodeMirror.fromTextArea(document.getElementById('dialogEd'), {
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

			    	#infos .CodeMirror{
						height: 15em !important;
						margin: 0px;
					}
				*/
				var diaCM;
				var win = bootbox.prompt({
						    title: "This is a prompt with a textarea!",
						    inputType: 'textarea',
						    callback: function (result) {
						        console.log(diaCM.getValue())
						        if(result != null){
						        	if(addParams){
						        		addParameters(editor,diaCM.getValue(),type,name);
						        	}else{
						        		addNewConsOrDes(editor,diaCM.getValue(),type,name);	
						        	}
						        	
						        }
						    }
						});
				win.on("shown.bs.modal", function() {
					console.log(win)
					console.log($('.modal-body'))
				    diaCM = CodeMirror.fromTextArea($(".bootbox-input-textarea")[0], {
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
			    	$('.modal-body').on('mousemove', function(e) {
				    //editor.on('mousemove', function(e) {
				    	console.log("MOVE MOVE")
				    	$('.preview').css({
						        'top' : e.pageY,
						        'left' : e.pageX
						      });
					});
			    	
			    	diaCM.on('keyup', function(event){

						var selector = document.querySelector('.modal-body');
						var cmLines = selector.querySelectorAll('.CodeMirror-line');
						for (var cml of cmLines) {
							console.log(cml);
							var dest = cml.querySelectorAll('.cm-destructor');
					        var cons = cml.querySelectorAll('.cm-cons');
					        var lDest = cml.querySelectorAll('.cm-local-destructor');
					        var lCons = cml.querySelectorAll('.cm-local-cons');
					        for(var d of dest){
					          d.addEventListener('mouseenter', function (e) {
					            console.log(this.textContent)
					            var name = this.textContent;
					            console.log(result.data.consAndDesMap[name])
					            if(result.data.consAndDesMap[name] == undefined){
					              $('.preview').css('visibility', 'hidden');
					              $('.preview').css('z-index', '2');
					            }else {
					              $('.preview').css('visibility', 'visible');
					              $('.preview').css('z-index', '9999');
					              $('.preview').empty().html(result.data.consAndDesMap[name]); 
					            }
					            
					          }, false); 

					          d.addEventListener('mouseleave', function (e) {
					            //console.log(this.textContent)
					            $('.preview').css('visibility', 'hidden');
					            $('.preview').css('z-index', '2');
					          }, false); 
					        }

					        for(var d of lDest){
					          d.addEventListener('mouseenter', function (e) {
					            console.log(this.textContent)
					            var name = this.textContent;
					            console.log(result.data.consAndDesMap[name])
					            if(result.data.consAndDesMap[name] == undefined){
					              $('.preview').css('visibility', 'hidden');
					              $('.preview').css('z-index', '2');
					            }else {
					              $('.preview').css('visibility', 'visible');
					              $('.preview').css('z-index', '9999');
					              $('.preview').empty().html(result.data.consAndDesMap[name]); 
					            }
					            
					          }, false); 

					          d.addEventListener('mouseleave', function (e) {
					            //console.log(this.textContent)
					            $('.preview').css('visibility', 'hidden');
					            $('.preview').css('z-index', '2');
					            
					          }, false); 
					        }

					        for(var c of cons){
					          c.addEventListener('mouseenter', function (e) {
					            console.log(this.textContent)
					            var name = this.textContent;
					            if(result.data.consAndDesMap[name] == undefined){
					              $('.preview').css('visibility', 'hidden');
					              $('.preview').css('z-index', '2');
					            } else {
					              $('.preview').css('visibility', 'visible');
					              $('.preview').css('z-index', '9999');
					              $('.preview').empty().html(result.data.consAndDesMap[name]);  
					            }
					           
					          }, false); 

					          c.addEventListener('mouseleave', function (e) {
					            //console.log(this.textContent)
					            $('.preview').css('visibility', 'hidden');
					            $('.preview').css('z-index', '2');
					            
					          }, false); 
					        }

					        for(var c of lCons){
					          c.addEventListener('mouseenter', function (e) {
					            console.log(this.textContent)
					            var name = this.textContent;
					            if(result.data.consAndDesMap[name] == undefined){
					              $('.preview').css('visibility', 'hidden');
					              $('.preview').css('z-index', '2');
					            } else {
					              $('.preview').css('visibility', 'visible');
					              $('.preview').css('z-index', '9999');
					              $('.preview').empty().html(result.data.consAndDesMap[name]);  
					            }
					           
					          }, false); 

					          c.addEventListener('mouseleave', function (e) {
					            //console.log(this.textContent)
					            $('.preview').css('visibility', 'hidden');
					            $('.preview').css('z-index', '2');
					            
					          }, false); 
					        }
						}
					});

					
					
			    	diaCM.setValue(body);
			    	
			    	diaCM.setCursor({line:diaCM.lastLine(),ch:0})
					diaCM.setSelection(diaCM.getCursor());
					diaCM.doc.replaceSelections([" "]);
					CodeMirror.signal(diaCM, "change",{from:{line:diaCM.lastLine,ch:0},to:{line:diaCM.lastLine,ch:1},text:[" "],removed:""});
			    	
					var selector = document.querySelector('.modal-body');
					var cmLines = selector.querySelectorAll('.CodeMirror-line');
					for (var cml of cmLines) {
						console.log(cml);
						var dest = cml.querySelectorAll('.cm-destructor');
				        var cons = cml.querySelectorAll('.cm-cons');
				        var lDest = cml.querySelectorAll('.cm-local-destructor');
				        var lCons = cml.querySelectorAll('.cm-local-cons');
				        for(var d of dest){
				          d.addEventListener('mouseenter', function (e) {
				            console.log(this.textContent)
				            var name = this.textContent;
				            console.log(result.data.consAndDesMap[name])
				            if(result.data.consAndDesMap[name] == undefined){
				              $('.preview').css('visibility', 'hidden');
				              $('.preview').css('z-index', '2');
				            }else {
				              $('.preview').css('visibility', 'visible');
				              $('.preview').css('z-index', '9999');
				              $('.preview').empty().html(result.data.consAndDesMap[name]); 
				            }
				            
				          }, false); 

				          d.addEventListener('mouseleave', function (e) {
				            //console.log(this.textContent)
				            $('.preview').css('visibility', 'hidden');
				            $('.preview').css('z-index', '2');
				          }, false); 
				        }

				        for(var d of lDest){
				          d.addEventListener('mouseenter', function (e) {
				            console.log(this.textContent)
				            var name = this.textContent;
				            console.log(result.data.consAndDesMap[name])
				            if(result.data.consAndDesMap[name] == undefined){
				              $('.preview').css('visibility', 'hidden');
				              $('.preview').css('z-index', '2');
				            }else {
				              $('.preview').css('visibility', 'visible');
				              $('.preview').css('z-index', '9999');
				              $('.preview').empty().html(result.data.consAndDesMap[name]); 
				            }
				            
				          }, false); 

				          d.addEventListener('mouseleave', function (e) {
				            //console.log(this.textContent)
				            $('.preview').css('visibility', 'hidden');
				            $('.preview').css('z-index', '2');
				            
				          }, false); 
				        }

				        for(var c of cons){
				          c.addEventListener('mouseenter', function (e) {
				            console.log(this.textContent)
				            var name = this.textContent;
				            if(result.data.consAndDesMap[name] == undefined){
				              $('.preview').css('visibility', 'hidden');
				              $('.preview').css('z-index', '2');
				            } else {
				              $('.preview').css('visibility', 'visible');
				              $('.preview').css('z-index', '9999');
				              $('.preview').empty().html(result.data.consAndDesMap[name]);  
				            }
				           
				          }, false); 

				          c.addEventListener('mouseleave', function (e) {
				            //console.log(this.textContent)
				            $('.preview').css('visibility', 'hidden');
				            $('.preview').css('z-index', '2');
				            
				          }, false); 
				        }

				        for(var c of lCons){
				          c.addEventListener('mouseenter', function (e) {
				            console.log(this.textContent)
				            var name = this.textContent;
				            if(result.data.consAndDesMap[name] == undefined){
				              $('.preview').css('visibility', 'hidden');
				              $('.preview').css('z-index', '2');
				            } else {
				              $('.preview').css('visibility', 'visible');
				              $('.preview').css('z-index', '9999');
				              $('.preview').empty().html(result.data.consAndDesMap[name]);  
				            }
				           
				          }, false); 

				          c.addEventListener('mouseleave', function (e) {
				            //console.log(this.textContent)
				            $('.preview').css('visibility', 'hidden');
				            $('.preview').css('z-index', '2');
				            
				          }, false); 
				        }
					}

					
			  //   	const ev = {
					//   type: 'keydown',
					//   keyCode: 13 // the keycode for the enter key, use any keycode here
					// }
					// diaCM.triggerOnKeyDown(ev)

				});

				win.modal("show");
				$('.preview').css('z-index', '2');
				$('.preview').css('visibility', 'hidden');
				/*bootbox.confirm(form, function(result) {
				        if(result)
				            $('#infos').submit();
				});*/
			} else {
				bootbox.alert({
				    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+result.data.error ,
				    callback: function () {
				        console.log('This was logged in the callback!');
				    }
				})

				editor.setValue(editor.getValue());
			}
			$('#runResult').val(result.data);
			
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val(JSON.stringify(e));		
		}
	});
}

function addParameters(editor,body,type,name){
	var params = {body:body, type:type, name:name};

	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/addParams",
		data : JSON.stringify(params),
		dataType : 'json',
		success : function(result) {
			if(result.status === "success"){
				editor.setValue(result.data);
			} else{
				editor.setValue(editor.getValue());
			}
			$('#runResult').val(result.data);
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val(JSON.stringify(e));		
		}
	});
}

function addNewConsOrDes(editor,body,type,name){
	var params = {body:body, type:type, name:name};

	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/addConsOrDes",
		data : JSON.stringify(params),
		dataType : 'json',
		success : function(result) {
			if(result.status === "success"){
				editor.setValue(result.data);
			} else{
				editor.setValue(editor.getValue());
			}
			$('#runResult').val(result.data);
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val(JSON.stringify(e));		
		}
	});
}

function completeFun(editor,token,cur,info){
	
	if(((info.type ==="consumer" || info.type ==="generator") && token.string === "=") ||
		((info.type ==="match" || info.type ==="comatch") && token.string === "with")){
		var l = info.line;
		var content = editor.getLine(l);
		for(var i = l+1;i<=cur.line;++i){
			content = content+" "+editor.getLine(i);
		}
		console.log("start: " +l + " end: "+cur.line+" " + content);
		var arr = content.split(/[\s:,()\[\]=]+/);
		console.log(arr)
		var t;
		var name;
		var j = 0;
		while(j<arr.length&&arr[j] !== "consumer" && arr[j] !== "generator" && arr[j] !== "match" && arr[j] !== "comatch"){
			arr.shift();
			//++j;
		}
		
		if(arr.length > 3){
			if(info.type==="consumer" && /^[A-Z]/.test(arr[2])){
				t = arr[2];
				
				var params = [];
				for(var i = 4;i<arr.length; i= i+2){
					if(/^[a-z]/.test(arr[i]))
						params.push(arr[i]);
				}
				autoCompleteBody(editor,"data",params ,t, cur,info.startCol);
				
			}else if(info.type==="generator"){
				var params = [];
				for(var i = 3;i<arr.length; i= i+2){
					if(/^[a-z]/.test(arr[i]))
						params.push(arr[i]);
				}
				var idx = 3+2*params.length;
				if(/^[A-Z]/.test(arr[idx])){
					t = arr[idx];
					
					autoCompleteBody(editor,"codata", params,t, cur,info.startCol)
				}
			} else if(info.type==="match"){
				var idx = 0;
				for(var i=0;i<arr.length;++i){
					if(arr[i] === "match")
						idx = i;
				}
				++idx;
				if(/^[A-Z]/.test(arr[idx])){
					t = arr[idx];
				
					var params = [];
				
					autoCompleteBody(editor,"data",params ,t, cur,info.startCol);
				}
			} else if(info.type==="comatch"){
				var idx = 0;
				for(var i=0;i<arr.length;++i){
					if(arr[i] === "comatch")
						idx = i;
				}
				++idx;
				if(/^[A-Z]/.test(arr[idx])){
					t = arr[idx];
				
					var params = [];
				
					autoCompleteBody(editor,"codata",params ,t, cur,info.startCol);
				}
			}

		}
		console.log(arr)
		console.log(t)
		return {line: -1, type:""};
	}
	return info;
}

function autoCompleteBody(editor,funType, vars,typeName, cur,startCol){
	var params = {
			type : funType,
			vars: vars,
			typename: typeName,
			start: startCol,
			col: cur.ch
	}
	
	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/autocomplete",
		data : JSON.stringify(params),
		dataType : 'json',
		success : function(result) {
			if(result.status == "success"){
				var res = JSON.parse(result.data);
				var toAdd = res.result;
				var col = res.col;

				editor.replaceRange(toAdd, cur);
				editor.setCursor({line:cur.line+1,ch:col});

			}
			$('#runResult').val(result.data.result);
			
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val(JSON.stringify(e));		
		}
	});
}

$(function () {
	  $('[data-toggle="tooltip"]').tooltip();
})

function saveFile(name, editor){
	var prog = editor.getValue();
    var textFileAsBlob = new Blob([prog], {type:'text/plain'});
    var fileName = name + ".ub";
    
    var downloadLink = document.createElement("a");
    downloadLink.download = fileName;
    downloadLink.innerHTML = "Save source file";
    if (window.URL != null)
    {
        // Chrome allows the link to be clicked
        // without actually adding it to the DOM.
        downloadLink.href = window.URL.createObjectURL(textFileAsBlob);
    }
    else
    {
        // Firefox requires the link to be added to the DOM
        // before it can be clicked.
        downloadLink.href = window.URL.createObjectURL(textFileAsBlob);
        downloadLink.onclick = destroyClickedElement;
        downloadLink.style.display = "none";
        document.body.appendChild(downloadLink);
    }

    downloadLink.click();
}

/*------------------------------------------------------
---- Validate Result								----
-------------------------------------------------------*/
function validate(){
	var element = document.getElementById('runResult');
	var res = element.value;
	if(typeof res !== 'undefined'){
		if(res.includes('ERROR')){
			element.classList.add("error");
		} else {
			if(element.classList.contains("error")){
				element.classList.remove("error");
			}
		} 
	}
		
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


/*------------------------------------------------------
---- Terminal										----
-------------------------------------------------------*/
/*
jQuery(function($, undefined) {
	$('#term').terminal(function(command, term) {
		if(command !== ''){
			var cmd = {
					expr : command
			}
			$.ajax({
				type : "POST",
				contentType : "application/json",
				url : "api/exprEval",
				data : JSON.stringify(cmd),
				dataType : 'json',
				success : function(result) {
					if(result.status === 'error'){
						term.echo('[[b;red;]ERROR] ' + result.data);
					}else{
						term.echo(result.data);
					}
					
				},
				error : function(e) {
					console.log("ERROR: ", e);
					$('#runResult').val(JSON.stringify(e) + e.responseText);
					var response = JSON.parse(e.responseText);
					console.log("ERROR: ", response);
					term.echo('[[b;red;]ERROR] ' + response.error);
				}
			});
//			var response = $.post('api/exprEval?expr='+command, {command: command});
//			var jsonRes = JSON.parse(response);
//			if('error' in jsonRes){
//				return '[[b;red]ERROR]' + jsonRes.error;
//			}
//			return jsonRes.result;
		}else {
			return '';
		}
    },
    {
        greetings:    " /$$   /$$                     /$$                                    \n" +
		        	  "| $$  | $$                    | $$                                    \n" +
		        	  "| $$  | $$  /$$$$$$   /$$$$$$ | $$$$$$$   /$$$$$$   /$$$$$$   /$$$$$$ \n" +
		        	  "| $$  | $$ /$$__  $$ /$$__  $$| $$__  $$ /$$__  $$ /$$__  $$ /$$__  $$\n" +
		        	  "| $$  | $$| $$  \\__/| $$  \\ $$| $$  \\ $$| $$  \\ $$| $$  \\__/| $$  \\ $$\n" +
		        	  "| $$  | $$| $$      | $$  | $$| $$  | $$| $$  | $$| $$      | $$  | $$\n" +
		        	  "|  $$$$$$/| $$      |  $$$$$$/| $$$$$$$/|  $$$$$$/| $$      |  $$$$$$/\n" +
		        	  " \\______/ |__/       \\______/ |_______/  \\______/ |__/       \\______/ \n",
        name: 'uroboro_repl',
        height: 200,
        prompt: 'uroboro> '
    });
	
	$.terminal.syntax('javascript');
});
*/
/*------------------------------------------------------
---- Destructorize								----
-------------------------------------------------------*/
function refunc(cmEditor){
	// var editor = {
	// 		value : cmEditor.getValue(),
	// 		result: ""
	// }

	//from local storage
	//var allData = window.program[0][0];
	var allData = localStorage.getItem("data").split(",");
	if(allData[0] === ""){
		bootbox.alert({
		    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+"There are no declared data types" ,
		    callback: function () {
		        console.log('This was logged in the callback!');
		    }
		})
	}else{
		var opt = [ {text: 'Choose one...',value: '',}];

		for (var index = 0; index < allData.length; ++index) {
		    opt.push({text: allData[index], value: allData[index],});
		}

		bootbox.prompt({
		    title: "Choose data type ...",
		    inputType: 'select',
		    inputOptions: opt,
		    callback: function (result) {
		        console.log(result);
		        if(result !== null){
		        	if(result === ""){
		        		var element = document.getElementsByClassName("bootbox-input-select")[0];
		        		element.classList.add('error');
		        		return false;
		        	} else{
			        	doRefunc(cmEditor, result);
			        }
		        }
		    }
		});
	}
	// $.ajax({
	// 	type : "POST",
	// 	contentType : "application/json",
	// 	url : "api/allData?trans=refunc",
	// 	data : JSON.stringify(editor),
	// 	dataType : 'json',
	// 	success : function(refResult) {
	// 		removeErrorClass();
	// 		console.log(refResult.data);
	// 		if(refResult.status == "success"){
	// 			//var allData = JSON.parse(refResult.data);
	// 			var allData = window.program[0][0];
	// 			var opt = [ {text: 'Choose one...',value: '',}];
				
	// 			for (var index = 0; index < allData.length; ++index) {
	// 			    opt.push({text: allData[index], value: allData[index],});
	// 			}
				
	// 			bootbox.prompt({
	// 			    title: "Choose data type ...",
	// 			    inputType: 'select',
	// 			    inputOptions: opt,
	// 			    callback: function (result) {
	// 			        console.log(result);
	// 			        if(result !== null)
	// 			        	doRefunc(cmEditor, result);
	// 			    }
	// 			});

				
	// 		}else{
	// 			var element = document.getElementById('runResult');
	// 			element.classList.add('error');
	// 		}
	// 		$('#runResult').val(refResult.data);
			
	// 	},
	// 	error : function(e) {
	// 		console.log("ERROR: ", e);
	// 		$('#runResult').val(JSON.stringify(e));		
	// 	}
	// });
	
}

function doRefunc(cmEditor,typename){
	var params = {
			type : "refunc",
			typename: typename
	}
	
	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/transformation",
		data : JSON.stringify(params),
		dataType : 'json',
		success : function(refResult) {
			if(refResult.status == "success"){
				cmEditor.setValue(refResult.data.source);
				$('#runResult').val(refResult.data.oldSource);
			} else {
				var element = document.getElementById('runResult');
				 if(element.classList.contains("Succ")){
				    element.classList.remove("Succ");
				  }
				element.classList.add('error');
				$('#runResult').val(refResult.data.error);
			}
			
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val('Error '+JSON.stringify(e));		
		}
	});
}

/*------------------------------------------------------
---- Constructorize								----
-------------------------------------------------------*/
function defunc(cmEditor){
	// var editor = {
	// 		value : cmEditor.getValue(),
	// 		result: ""
	// }

	//var allData = window.program[0][2];
	var allData = localStorage.getItem('codata').split(",");
	if(allData[0] === ""){
		bootbox.alert({
		    message: '<i class="fas fa-exclamation-triangle fa-lg" style="color:#dc3545!important;"></i> '+"There are no declared codata types" ,
		    callback: function () {
		        console.log('This was logged in the callback!');
		    }
		})
	}else{
		var opt = [ {text: 'Choose one...',value: '',}];
	
		for (var index = 0; index < allData.length; ++index) {
		    opt.push({text: allData[index], value: allData[index],});
		}
		
		bootbox.prompt({
		    title: "Choose codata type ...",
		    inputType: 'select',
		    inputOptions: opt,
		    callback: function (result) {
		        console.log(result);
		        if(result !== null){
		        	if(result === ""){
		        		var element = document.getElementsByClassName("bootbox-input-select")[0];
		        		element.classList.add('error');
		        		return false;
		        	} else{
		        		doDefunc(cmEditor, result);
		        	}
		        }
		    }
		});
	}
	
	// $.ajax({
	// 	type : "POST",
	// 	contentType : "application/json",
	// 	url : "api/allData?trans=defunc",
	// 	data : JSON.stringify(editor),
	// 	dataType : 'json',
	// 	success : function(defResult) {
	// 		removeErrorClass();
	// 		console.log(defResult.data);
	// 		if(defResult.status == "success"){
	// 			var allData = JSON.parse(defResult.data);
	// 			var opt = [ {text: 'Choose one...',value: '',}];
				
	// 			for (var index = 0; index < allData.length; ++index) {
	// 			    opt.push({text: allData[index], value: allData[index],});
	// 			}
				
	// 			bootbox.prompt({
	// 			    title: "Choose codata type ...",
	// 			    inputType: 'select',
	// 			    inputOptions: opt,
	// 			    callback: function (result) {
	// 			        console.log(result);
	// 			        if(result !== null)
	// 			        	doDefunc(cmEditor, result);
	// 			    }
	// 			});

				
	// 		}else{
	// 			var element = document.getElementById('runResult');
	// 			element.classList.add('error');
	// 		}
	// 		$('#runResult').val(defResult.data);
			
	// 	},
	// 	error : function(e) {
	// 		console.log("ERROR: ", e);
	// 		$('#runResult').val(JSON.stringify(e));		
	// 	}
	// });
	
}

function doDefunc(cmEditor,typename){
	var params = {
			type : "defunc",
			typename: typename
	}
	
	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/transformation",
		data : JSON.stringify(params),
		dataType : 'json',
		success : function(defResult) {
			if(defResult.status == "success"){
				cmEditor.setValue(defResult.data.source);
				$('#runResult').val(defResult.data.oldSource);
			} else {
				var element = document.getElementById('runResult');

			  if(element.classList.contains("Succ")){
			    element.classList.remove("Succ");
			  }
				element.classList.add('error');
				$('#runResult').val(defResult.data.error);
			}
			
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val(JSON.stringify(e));		
		}
	});
}

/*------------------------------------------------------
---- Parse Programm									----
-------------------------------------------------------*/
function parseProg(cmEditor){
//	var dialog = bootbox.dialog({
//	    title: 'A custom dialog with init',
//	    message: '<p><i class="fa fa-spin fa-spinner"></i> Loading...</p>'
//	});
		
	var editor = {
			value : cmEditor.getValue(),
			result: ""
	}
	
	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/parse",
		data : JSON.stringify(editor),
		dataType : 'json',
		success : function(result) {
			if(result.status === 'error'){
				var element = document.getElementById('runResult');
				element.classList.add('error');
			}else{
				removeErrorClass();
			}
			
			$('#runResult').val(result.data.result);
			
		},
		error : function(e) {
			console.log("ERROR: ", e);
			$('#runResult').val(JSON.stringify(e));		
		}
	});

}

/*------------------------------------------------------
---- Set pretty print								----
-------------------------------------------------------*/
function setConfig(){
//	var dialog = bootbox.dialog({
//	    message: '<p class="text-center">Please wait while we do something...</p>',
//	    closeButton: true
//	});
	$.ajax({
		type : "POST",
		contentType : "application/json",
		url : "api/config",
		dataType : 'json',
		success : function(confResult) {
			if(confResult.status == "success"){
				var conf = JSON.parse(confResult.data);
				var val = [];
				
				for (var index = 0; index < conf.length; ++index) {
				    val.push(conf[index]);
				}
				
				bootbox.prompt({
				    title: 'Choose your pretty print config ...',
				    value: val,
				    inputType: "checkbox",
				    inputOptions: [
				        {
				            text: 'Print qualified names',
				            value: 'printQualifiedNames',
				        },
				        {
				            text: 'Print values of type Nat are printed as numerals',
				            value: 'printNat',
				        },
				        {
				            text: 'List order reversed',
				            value: 'listOrderReversed',
				        },
				        {
				            text: 'Print deBruijn Index of variables',
				            value: 'printDeBruijn',
				        }
				    ],
				    callback: function (result) {
				        console.log(result);
				        if(result !== null && !arraysEqual(result,val)){
				        	doSetConf(result);
				        }
				        
				    }
				});
			}
			
		},
		error : function(e) {
			console.log("ERROR: ", e);
		}
	});
}

function doSetConf(conf){
	var config = {
		printQualifiedNames : conf.includes("printQualifiedNames"),
		printNat : conf.includes("printNat"),
		listOrderReversed : conf.includes("listOrderReversed"),
		printDeBruijn : conf.includes("printDeBruijn")
	}
	console.log(config);
	$.ajax({
	type : "POST",
	contentType : "application/json",
	url : "api/setConfig",
	data : JSON.stringify(config),
	dataType : 'json',
	success : function(result) {
		console.log(result);
		Notification.show(result.data);
	},
	error : function(e) {
		console.log("ERROR: ", e);
	}
	});
}


function removeErrorClass(){
	var element = document.getElementById('runResult');
	
	if(element.classList.contains("error")){
		element.classList.remove("error");
	}	
}

function arraysEqual(a, b) {
  if (a === b) return true;
  if (a == null || b == null) return false;
  if (a.length != b.length) return false;

  for (var i = 0; i < a.length; ++i) {
    if (a[i] !== b[i]) return false;
  }
  
  return true;
}

function arrContains(arr,elem){
	
	for(var i=0;i<arr.length;++i){
		if(arr[i] === elem)
			return true;
	}
	return false;
}

