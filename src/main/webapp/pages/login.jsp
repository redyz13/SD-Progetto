
<!DOCTYPE html>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta http-equiv="X-UA-Compatible" content="IE=edge">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Login</title>
    <link rel="stylesheet" href="${pageContext.request.contextPath}/css/login.css">
</head>
<body>
<%@ include file="header.jsp" %>
<script src="${pageContext.request.contextPath}/js/changeForm.js"></script>
<div class="logSig">
	<img src="${pageContext.request.contextPath}/images/system/logSig.png" id="imgLogSig" alt="Logo">
	<div class="form-container">
			<form action="${pageContext.request.contextPath}/Login" method="post" id="lform">
			    <p id="head">Accedi</p>
			    <p>Non ti sei ancora registrato? <a href='javascript:changeForm("Sign Up")'>Registrati ora!</a></p> 
			    <div class="group">      
      				<input type="text" name="username" id="username" required>
      				<label for="username">Username</label>
    			</div>
    			<div class="group">      
      				<input type="password" name="password" id="password" required>
      				<label for="password">Password</label>
    			</div>
			    <br><button type="submit" class="button2">Accedi</button>
			</form>
			<form action="${pageContext.request.contextPath}/Registrazione" method="post" id="sform">
			    <p id="head">Registrati</p>
		        <p>Sei gi&agrave; registrato? <a href='javascript:changeForm("Log In")'>Accedi ora!</a></p> 
			    <div class="group">      
      				<input type="text" name="usernameReg" id="usernameReg" required>
      				<label for="usernameReg">Username</label>
    			</div>
    			<div class="group">      
      				<input type="password" name="passwordReg" id="passwordReg" required>
      				<label for="passwordReg">Password</label>
    			</div>
    			<div class="group">      
      				<input type="text" name="nomeReg" id="nomeReg" required>
      				<label for="nomeReg">Nome</label>
    			</div>
    			<div class="group">      
      				<input type="text" name="cognomeReg" id="cognomeReg" required>
      				<label for="cognomeReg">Cognome</label>
    			</div>
    			<div class="group" id="email">
      				<input type="text" name="emailReg" id="emailReg" required>
      				<label for="emailReg">Email</label>

    			</div>
    			<div class="group">      
      				<input type="date" name="dataNascitaReg" id="dataNascitaReg" required>
      				<label for="dataNascitaReg">Data di Nascita</label>
    			</div>
		        <input type="hidden" name="tipo" value="user">
		        <br> <button type="submit" class="button3">Registrati</button><br><br>
				<div class="non-valida"></div>
			</form>
	</div>
</div>
<script>
	document.getElementById("lform").style.display = "block";
	document.getElementById("sform").style.display = "none";
</script>
<% if (session.getAttribute("utentePresente") != null  && session.getAttribute("utentePresente").equals(false)) { %>
<p>Utente registrato correttamente!</p>
<% } else if (session.getAttribute("utentePresente")!= null && session.getAttribute("utentePresente").equals(true)) { %>
<p>Username o email gi&#224 in uso</p>
<% }
    session.removeAttribute("utentePresente");
%>

<%@ include file="footer.jsp" %>
<script src="${pageContext.request.contextPath}/js/regexReg.js"></script>
</body>
</html>
