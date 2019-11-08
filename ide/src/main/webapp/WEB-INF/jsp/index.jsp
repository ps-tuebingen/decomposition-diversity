<%@ page language="java" contentType="text/html; charset=UTF-8"
	pageEncoding="UTF-8"%>
<%@ taglib prefix="spring" uri="http://www.springframework.org/tags"%>
<%@ taglib prefix="form" uri="http://www.springframework.org/tags/form"%>

<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>Decomposition Diversity</title>
<spring:url value="/resources/codemirror/lib/codemirror.css" var="cmCSS" />
<spring:url value="/resources/bootstrap/css/bootstrap.min.css"
	var="bootCSS" />
<spring:url value="/resources/css/editor.css" var="editorCSS" />
<spring:url value="/resources/codemirror/theme/uroboro.css" var="theme" />
<spring:url value="/resources/codemirror/addon/hint/show-hint.css"
	var="autoCSS" />
<spring:url value="/resources/codemirror/addon/hint/templates-hint.css"
	var="tempCSS" />
<spring:url
	value="/resources/codemirror/addon/hint/show-context-info.css"
	var="contextCSS" />
<spring:url value="/resources/codemirror/addon/lint/lint.css"
	var="lintCSS" />
<!--<spring:url value="https://cdn.jsdelivr.net/npm/jquery.terminal@2.0.0/css/jquery.terminal.min.css" var="termCSS" />-->
<!--<spring:url value="https://unpkg.com/prismjs/themes/prism.css" var="prismCSS" />-->
<spring:url value="/resources/fontawesome/css/all.css" var="fontCSS" />
<spring:url
	value="https://cdnjs.cloudflare.com/ajax/libs/jquery-contextmenu/2.7.1/jquery.contextMenu.min.css"
	var="ctxMenuCSS" />

<spring:url value="/resources/js/jquery-3.3.1.min.js" var="jquery" />
<spring:url value="https://cdn.jsdelivr.net/npm/jquery-validation@1.19.0/dist/jquery.validate.min.js" var="jqueryValid" />

<spring:url value="/resources/js/editor.js" var="editor" />
<spring:url value="/resources/codemirror/lib/codemirror.js" var="cmJS" />
<spring:url value="/resources/codemirror/addon/edit/matchbrackets.js"
	var="matchB" />
<spring:url value="/resources/codemirror/addon/edit/closebrackets.js"
	var="closeB" />
<spring:url value="/resources/codemirror/mode/uroboro.js" var="urobMode" />
<spring:url value="/resources/codemirror/addon/selection/active-line.js"
	var="actLine" />
<spring:url value="/resources/codemirror/addon/hint/show-hint.js"
	var="autoC" />
<!--<spring:url value="/resources/codemirror/addon/hint/anyword-hint.js" var="autoAny" />-->
<spring:url value="/resources/codemirror/addon/hint/uroboro-hint.js"
	var="autoUro" />
<spring:url value="/resources/codemirror/addon/hint/temp-hint.js"
	var="temph" />
<spring:url
	value="/resources/codemirror/addon/hint/show-context-info.js"
	var="context" />
<spring:url value="/resources/codemirror/addon/hint/uroboro-temps.js"
	var="utemp" />
<spring:url
	value="/resources/codemirror/addon/search/match-highlighter.js"
	var="mh" />
<spring:url value="/resources/codemirror/addon/search/searchcursor.js"
	var="sc" />
<spring:url value="/resources/codemirror/addon/search/search.js"
	var="search" />
<spring:url
	value="/resources/codemirror/addon/search/matchesonscrollbar.js"
	var="mos" />
<spring:url
	value="/resources/codemirror/addon/scroll/annotatescrollbar.js"
	var="as" />
<spring:url value="/resources/codemirror/addon/lint/lint.js"
	var="lintJS" />
<spring:url value="/resources/codemirror/addon/lint/uroboro-lint.js"
	var="lintUR" />

<!--<spring:url value="https://cdn.jsdelivr.net/npm/jquery.terminal@2.0.0/js/jquery.terminal.min.js" var="termJS"/>-->
<spring:url value="/resources/js/popper.min.js" var="popperJS" />
<spring:url value="/resources/bootstrap/js/bootstrap.min.js"
	var="bootJS" />
<spring:url value="/resources/js/bootbox.min.js" var="bootbox" />
<spring:url value="/resources/fontawesome/js/all.js" var="fontJS" />
<spring:url
	value="https://cdnjs.cloudflare.com/ajax/libs/jquery-contextmenu/2.7.1/jquery.contextMenu.min.js"
	var="ctxMenu" />
<spring:url
	value="https://cdnjs.cloudflare.com/ajax/libs/jquery-contextmenu/2.7.1/jquery.ui.position.js"
	var="ctxMenuPos" />
<!--<spring:url value="https://unpkg.com/prismjs/prism.js" var="prism" />-->
<!--<spring:url value="https://unpkg.com/jquery.terminal@1.x.x/js/prism.js" var="prismTer" />-->

<link href="${cmCSS}" rel="stylesheet" />
<link href="${termCSS}" rel="stylesheet" />
<link href="${bootCSS}" rel="stylesheet" />
<link href="${editorCSS}" rel="stylesheet" />
<link href="${autoCSS}" rel="stylesheet" />
<link href="${lintCSS}" rel="stylesheet" />
<link href="${hoverCSS}" rel="stylesheet" />
<link href="${theme}" rel="stylesheet" />
<!-- <link href="${prismCSS}" rel="stylesheet" />-->
<link href="${fontCSS}" rel="stylesheet" />
<link href="${ctxMenuCSS}" rel="stylesheet" />
<!-- <link href="${tempCSS}" rel="stylesheet" />
	<link href="${contextCSS}" rel="stylesheet" />-->

<script src="${jquery}"></script>
<script src="${jqueryValid}"></script>

<!-- <script src="${termJS}"></script> -->
<script src="${cmJS}"></script>
<script src="${matchB}"></script>
<script src="${closeB}"></script>
<script src="${actLine}"></script>
<script src="${autoC}"></script>
<script src="${lintJS}"></script>
<script src="${lintUR}"></script>

<!--  <script src="${temph}"></script>
	<script src="${context}"></script>-->

<!-- <script src="${autoAny}"></script> -->
<script src="${autoUro}"></script>

<script src="${mh}"></script>
<script src="${sc}"></script>
<script src="${search}"></script>
<script src="${mos}"></script>
<script src="${as}"></script>
<script src="${urobMode}"></script>
<script src="${popperJS}"></script>
<script src="${bootJS}"></script>
<script src="${bootbox}"></script>
<script src="${fontJS}"></script>
<script src="${ctxMenu}"></script>
<script src="${ctxMenuPos}"></script>
<!-- <script src="${prism}"></script> -->
<!-- <script src="${prismTer}"></script>-->

<!-- <script src="${utemp}"></script>-->
<script src="${editor}"></script>
</head>
<body onLoad="window.scroll(0,0)">
	<div id="header">
		<!-- Image and text -->
		<nav class="navbar navbar-dark bg-blue">
			<a class="navbar-brand" href="#"> <!--  <img src="/docs/4.1/assets/brand/bootstrap-solid.svg" width="30" height="30" class="d-inline-block align-top" alt="">-->
				--- Decomposition Diversity IDE ---
			</a>
		</nav>
	</div>

	<div class="container-fluid">
		<!--  <div class="card">
		<div class="card-body">-->
		<form:form method="POST" modelAttribute="editor">

			<div class="form-row">

				<!--  <div class="col"> -->
				<div class="ide-btn-gruop p-3 mb-5 bg-white rounded">
					<div class="btn-group">
						<button class="btn btn-blue dropdown-toggle" type="button"
							data-toggle="dropdown" aria-haspopup="true" aria-expanded="false"
							id="transformation">Transformer</button>
						<div class="dropdown-menu">
							<button class="dropdown-item" type="button" id="refuncBtn">Destructorize</button>
							<button class="dropdown-item" type="button" id="defuncBtn">Constructorize</button>
						</div>
					</div>
					<!-- <input type="submit" class="btn btn-success" id="parseBtn" value="Parse"/> -->
					<!-- <button type="submit" class="btn btn-blue" id="refuncBtn" disabled>Destructorize</button>
					<input type="submit" class="btn btn-blue" id="defuncBtn"
					 	value="Constructorize" disabled />-->
					<button class="btn btn-blue" id="stepp" disabled>Start
						stepper</button>
					<!-- <div class="dropdown">-->
					<div class="btn-group">
						<button class="btn btn-blue dropdown-toggle" type="button"
							data-toggle="dropdown" aria-haspopup="true" aria-expanded="false"
							id="source">Source</button>
						<div class="dropdown-menu">
							<button class="dropdown-item" type="button" id="addCons">Add
								constructor</button>
							<button class="dropdown-item" type="button" id="addDes">Add
								destructor</button>
							<button class="dropdown-item" type="button" id="removeCons">Remove
								constructor</button>
							<button class="dropdown-item" type="button" id="removeDes">Remove
								destructor</button>
							<button class="dropdown-item" type="button" id="formatBtn">Annotate
								types</button>
							

						</div>
					</div>

					<!-- </div>-->
					<!-- <button class="btn btn-secondary" id="setConf">Set printer config</button>-->
					<!--  </div>-->
				</div>

			</div>
			<div class="row">
				<div class="col-1 icons">
					<div class="edit-icons mb-5 bg-white">
						<button class="btn btn-secondary btn-sm btn-ic" id="save"
							data-toggle="tooltip" data-placement="left" title="Save" disabled>
							<i class="fas fa-save fa-2x ic"></i>
						</button>
						<div class="icon-upload">
							<label id="lab" for="upload"> <i
								class="fas fa-file-upload fa-2x ic" data-toggle="tooltip"
								data-placement="left" title="Upload source file"></i>
							</label> <input type="file" class="btn btn-secondary btn-sm btn-ic"
								id="upload" multiple />
						</div>
						<button class="btn btn-secondary btn-sm btn-ic" id="trash"
							data-toggle="tooltip" data-placement="left"
							title="Clear the content of the editor" disabled>
							<i class="fas fa-trash-alt fa-2x ic"></i>
						</button>

					</div>
				</div>
				<div class="col-sm-8 source">
					<div class="title-style">
						<i class="fas fa-file-code"></i> <label class="title">Source
							code</label>
					</div>
					<div id="sourceCode">
						<form:textarea path="value" class="form-control" id="editor" />
					</div>
				</div>


				<div class="col-4 res-col">

					<div class="form-group has-error">
						<div class="title-style">
							<i class="fas fa-cogs"></i> <label class="title">Result</label>
						</div>
						<form:textarea path="result" class="form-control" id="runResult"
							readonly="true" />
					</div>




				</div>


			</div>

		</form:form>
		<!--
			<div class="row">
				<div class="col">
				
						<div class="font-weight-bold">
							<i class="fas fa-terminal"></i>
							<label class="title">Expression evaluator</label>
						</div>
						
						<div id="term" class="terminal"></div>
						
						
							
					</div>
			</div>
			
		<!--  </div>
	</div>-->

	</div>
	<div id="msg" class="bb-alert msgbox alert alert-success"
		style="display: none;">
		<span>Info message</span>
	</div>
	<div class="footer" id="iFooter">
		<div class="container">Decomposition Diversity - &copy; 2019 Fayez Abu Alia</div>

	</div>


</body>
</html>
