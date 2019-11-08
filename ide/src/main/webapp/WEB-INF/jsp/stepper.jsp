<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>

<%@ taglib prefix="spring" uri="http://www.springframework.org/tags"%>
<%@ taglib prefix="form" uri="http://www.springframework.org/tags/form"%>

<!DOCTYPE html>
<html>
<head>
	<meta charset="UTF-8">
	<title>Stepper</title>

	<spring:url value="/resources/codemirror/lib/codemirror.css" var="cmCSS" />
	<spring:url value="/resources/bootstrap/css/bootstrap.min.css" var="bootCSS" />
	<spring:url value="/resources/css/editor.css" var="editorCSS" />
	<spring:url value="/resources/codemirror/theme/uroboro.css" var="theme" />
	<spring:url value="/resources/codemirror/theme/eval.css" var="themeEval" />
	<spring:url value="/resources/codemirror/addon/hint/show-hint.css" var="autoCSS" />
	<spring:url value="/resources/fontawesome/css/all.css" var="fontCSS" />
	
	
	<spring:url value="/resources/js/jquery-3.3.1.min.js" var="jquery" />
	<spring:url value="/resources/js/stepper.js" var="stepperJS" />
	<spring:url value="/resources/codemirror/lib/codemirror.js" var="cmJS" />
	<spring:url value="/resources/codemirror/addon/edit/matchbrackets.js" var="matchB" />
	<spring:url value="/resources/codemirror/addon/edit/closebrackets.js" var="closeB" />
	<spring:url value="/resources/codemirror/mode/uroboro.js" var="urobMode" />
	<spring:url value="/resources/codemirror/addon/selection/active-line.js" var="actLine" />
	<spring:url value="/resources/codemirror/addon/hint/show-hint.js" var="autoC" />
	<!--<spring:url value="/resources/codemirror/addon/hint/anyword-hint.js" var="autoAny" />-->
	<spring:url value="/resources/codemirror/addon/hint/uroboro-hint.js" var="autoUro" />
	<spring:url value="/resources/codemirror/addon/search/match-highlighter.js" var="mh" />
	<spring:url value="/resources/codemirror/addon/search/searchcursor.js" var="sc" />
	<spring:url value="/resources/codemirror/addon/search/matchesonscrollbar.js" var="mos" />
	<spring:url value="/resources/codemirror/addon/scroll/annotatescrollbar.js" var="as" />
	<spring:url value="/resources/js/popper.min.js" var="popperJS" />
	<spring:url value="/resources/bootstrap/js/bootstrap.min.js" var="bootJS" />
	<spring:url value="/resources/js/bootbox.min.js" var="bootbox" />
	<spring:url value="/resources/fontawesome/js/all.js" var="fontJS" />
	
	<link href="${cmCSS}" rel="stylesheet" />
	<link href="${bootCSS}" rel="stylesheet" />
	<link href="${editorCSS}" rel="stylesheet" />
	<link href="${autoCSS}" rel="stylesheet" />
	<link href="${theme}" rel="stylesheet" />
	<link href="${themeEval}" rel="stylesheet" />
	<link href="${fontCSS}" rel="stylesheet" />
	

	<script src="${jquery}"></script>
	<script src="${stepperJS}"></script>
	<script src="${cmJS}"></script>
	<script src="${matchB}"></script>
	<script src="${closeB}"></script>
	<script src="${actLine}"></script>
	<script src="${autoC}"></script>
	<!-- <script src="${autoAny}"></script> -->
	<script src="${autoUro}"></script>
	<script src="${mh}"></script>
	<script src="${sc}"></script>
	<script src="${mos}"></script>
	<script src="${as}"></script>
	<script src="${urobMode}"></script>
	<script src="${popperJS}"></script>
	<script src="${bootJS}"></script>
	<script src="${bootbox}"></script>
	<script src="${fontJS}"></script>
	
</head>
<body>
	<div id="header">
		<!-- Image and text -->
		<nav class="navbar navbar-dark bg-blue">
		  <a class="navbar-brand" href="#">
		    <!--  <img src="/docs/4.1/assets/brand/bootstrap-solid.svg" width="30" height="30" class="d-inline-block align-top" alt="">-->
		    --- Decomposition Diversity Stepper ---
		  </a>
		</nav>
	</div>
	<div id="msg" class="bb-alert msgbox alert alert-danger msgbox-error" style="display: none;">
        <span>Info message</span>
    </div>
	<div class="container-fluid">
		<form:form method="POST" modelAttribute="editor">
			<!--  <div class="card">
				<div class="card-body">-->
					<div class="form-row">
						<div id="stepper-btn-group">
							<button class="btn btn-lg stepper-btn" id="prev" data-toggle="tooltip" data-placement="bottom" title="Step backward" disabled><i class="fas fa-step-backward"></i></button>
							<button class="btn btn-lg stepper-btn" id="run" data-toggle="tooltip" data-placement="bottom" title="Run"><i class="fas fa-play"></i></button>
							<button class="btn btn-lg stepper-btn" id="step" data-toggle="tooltip" data-placement="bottom" title="Step forward" disabled><i class="fas fa-step-forward"></i></button>
							<button class="btn btn-lg stepper-btn-danger" id="stop" data-toggle="tooltip" data-placement="bottom" title="Clear" disabled><i class="fas fa-stop"></i></button>
						</div>
					</div>
				<!--</div>
			</div>-->
			<!-- <div class="card">
				<div class="card-body">-->
					<div class="row">
						<div class="col fixed">
							<form:textarea path="value" class="form-control" id="cm_editor"/>
						</div>
						<div class="col fixed">
							<form:textarea path="result" class="form-control" id="cmEditor_ReadOnly"/>
						</div>
					</div>
				<!--  </div>
			</div>-->
			
			
		</form:form>
	</div>
	<div class="footer" id="sFooter">
	</div>
</body>
</html>
