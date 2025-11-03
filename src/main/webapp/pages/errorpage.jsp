<%@ page import="java.io.StringWriter" %>
<%@ page import="java.io.PrintWriter" %>
<%@ page isErrorPage = "true" %>

<% StringWriter sw = new StringWriter(); exception.printStackTrace(new PrintWriter(sw)); %>

<!DOCTYPE html>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta http-equiv="X-UA-Compatible" content="IE=edge">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <link rel="stylesheet" 	href="${pageContext.request.contextPath}/css/errorPage.css">
    <title>Errore</title>
</head>
<body>
<%@ include file="header.jsp"%>
<div class="error-container">
    <img class="error-image" src="${pageContext.request.contextPath}/images/system/errorRobot.jpg" alt="Error Robot">
    <p class="error-message">Oops! Qualcosa &egrave andato storto</p>
    <a href="${pageContext.request.contextPath}/index.jsp"> <button class="error-button">Torna alla Home</button></a>
</div>

<%@ include file="footer.jsp"%>
</body>
</html>
