<%@ page import="java.util.Collection" %>
<%@ page import="java.math.RoundingMode" %>
<%@ page import="java.text.DecimalFormat" %>
<%@ page import="model.maglietta.MagliettaBean" %>

<% Collection<?> magliette = (Collection<?>) request.getAttribute("maglietteTipo");
	if (magliette == null)
		response.sendRedirect("./Tipo");
%>

<!DOCTYPE html>
<html lang="it">

<head>
	<meta charset="UTF-8">
	<meta http-equiv="X-UA-Compatible" content="IE=edge">
	<meta name="viewport" content="width=device-width, initial-scale=1.0">
	<link rel="stylesheet" href="css/index.css">
	<title>Catalogo</title>
</head>

<body>
<%@ include file="pages/header.jsp" %>
<h1 class="index-header"> <a href="Catalogo">Catalogo</a> </h1>
<div class="dropdown b">
	<button class="dropbtn">Ordina per &dtrif;</button>
	<div class="dropdown-content">
		<a href="Catalogo?ordine=nome">Nome</a>
		<a href="Catalogo?ordine=prezzo">Prezzo</a>
		<a href="Catalogo?ordine=colore">Colore</a>
		<a href="Catalogo?ordine=tipo">Tipo</a>
	</div>
</div>
<br>
<div class="magliette">
	<%
		if (magliette != null && magliette.size() != 0) {
			DecimalFormat df = new DecimalFormat("#.##");
			df.setRoundingMode(RoundingMode.FLOOR);

			// Stampa catalogo
			for (Object o : magliette) {
				MagliettaBean maglietta = (MagliettaBean) o;
				String prezzo = df.format(maglietta.getPrezzo());

				if (prezzo.matches("[0-9]+"))
					prezzo += ".00";
	%>
	<div class="elemento">
		<table class="dettagli">
			<caption hidden>Catalogo</caption>
			<tr hidden>
				<th>Grafica</th>
				<th>Descrizione</th>
				<th>Bottoni</th>
			</tr>
			<tr>
				<td colspan="2" class="maglietta">
					<a href="${pageContext.request.contextPath}/DescrizioneMaglietta?id=<%= maglietta.getID() %>">
						<img src="<%= maglietta.getGrafica() %>" alt="<%= maglietta.getNome() %>"></a>
				</td>
			</tr>
			<tr>
				<td colspan="2">
					<%= maglietta.getTipo() %><br>
					<%= maglietta.getNome() %><br>
					&euro;&nbsp;<%= prezzo %> + <%= maglietta.getIVA() %> &percnt; IVA<br>
					Colore: <%= maglietta.getColore() %> <br>
				</td>
			</tr>
			<tr>
				<td class="bottoni" colspan="2">
					<form action="DescrizioneMaglietta" method="GET">
						<input type="hidden" name="id" value="<%= maglietta.getID() %>">
						<button class="btn-shine button" type="submit">
							<span>Mostra Descrizione</span>
							<script src="https://cdn.lordicon.com/bhenfmcm.js" integrity="sha384-VY539ll5TIagHE4WlmKaJKJ4gKxfKtGxK0MgVqVuFG4RXvATOK4KWfapoPR/PE9K" crossorigin="anonymous"></script>
							<lord-icon src="https://cdn.lordicon.com/msoeawqm.json" trigger="hover" colors="primary:#1663c7,secondary:#f24c00" stroke="120"></lord-icon>
						</button>
					</form>
					<div class="aggiungi-maglietta">
						<form action="AggiungiMaglietta" method="POST">
							<input type="hidden" name="ID" value="<%= maglietta.getID() %>">
							<button class="btn-shine button" type="submit">
								<span>Aggiungi al carrello</span>
								<script src="https://cdn.lordicon.com/bhenfmcm.js" integrity="sha384-VY539ll5TIagHE4WlmKaJKJ4gKxfKtGxK0MgVqVuFG4RXvATOK4KWfapoPR/PE9K" crossorigin="anonymous"></script>
								<lord-icon src="https://cdn.lordicon.com/dnoiydox.json" trigger="hover" colors="primary:#1663c7,secondary:#f24c00" stroke="85"></lord-icon>
							</button>
							<span class="taglie">
								<label><select name="taglia" class="button" id="size" required>
									<option value="XS" selected>XS</option>
									<option value="S">S</option>
									<option value="M">M</option>
									<option value="L">L</option>
									<option value="XL">XL</option>
									<option value="XXL">XXL</option>
								</select></label>
								</span>
						</form>
					</div>
				</td>
			</tr>
		</table>
	</div>
	<%
			// Parentesi del for e dell'if
		} } else {
	%>
	<p class="niente">Nessun prodotto disponibile</p>
	<script src="https://cdn.lordicon.com/bhenfmcm.js" integrity="sha384-VY539ll5TIagHE4WlmKaJKJ4gKxfKtGxK0MgVqVuFG4RXvATOK4KWfapoPR/PE9K" crossorigin="anonymous"></script>
	<lord-icon
			src="https://cdn.lordicon.com/imamsnbq.json"
			trigger="loop"
			delay="1500"
			colors="primary:#000000,secondary:#000000"
			stroke="85"
			style="width:25%;height:25%">
	</lord-icon>
	<% } %>
</div>
<%@ include file="pages/footer.jsp" %>
</body>

</html>
