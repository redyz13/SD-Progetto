<%@ page import="model.CarrelloModel"%>
<%@ page import="java.util.Collection"%>
<%@ page import="java.text.DecimalFormat"%>
<%@ page import="java.math.RoundingMode"%>
<%@ page import="model.maglietta.MagliettaOrdine"%>
<%@ page import="model.utente.UtenteBean"%>
<%@ page import="java.time.LocalDate"%>
<%@ page import="java.time.temporal.ChronoUnit"%>
<%@ page import="java.time.format.DateTimeFormatter"%>
<%@ page import="java.time.format.FormatStyle"%>
<%@ page contentType="text/html;charset=UTF-8" %>
<%
	CarrelloModel carrello = (CarrelloModel) session.getAttribute("carrello");
	Collection<?> oggettiCarrello = carrello.getCarrello();
%>

<!DOCTYPE html>
<html lang="it">
<head>
<meta charset="UTF-8">
<meta http-equiv="X-UA-Compatible" content="IE=edge">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Checkout</title>

<link rel="stylesheet"
	href="${pageContext.request.contextPath}/css/modificaPagamento.css">
<link rel="stylesheet"
	href="${pageContext.request.contextPath}/css/checkout.css">
</head>
<body>
	<%@ include file="header.jsp"%>
	<%
		float prezzoTot = 0;
	%>
	<table id="checkoutTable">
		<caption hidden>Tabella checkout</caption>
		<tr>
			<th><h1>Riepilogo Ordine</h1></th>
			<th><h1>Dettagli Ordine</h1></th>
		</tr>
		<tr>
			<td id="riepilogoOrdine">
				<div class="data-consegna">
					<%
						LocalDate prima = LocalDate.now().plus(15, ChronoUnit.DAYS);
						String primaData = prima.format(DateTimeFormatter.ofLocalizedDate(FormatStyle.SHORT));
						LocalDate seconda = prima.plus(2, ChronoUnit.DAYS);
						String secondaData = seconda.format(DateTimeFormatter.ofLocalizedDate(FormatStyle.SHORT));
					%>
					<p class="data-consegna-p">
						Data consegna:
						<%=primaData%>
						-
						<%=secondaData%></p>
				</div>

				<div class="box">
					<div class="metodo-di-pagamento">
						<div class="metodo-header">
							<h3>Metodo di pagamento:</h3>
						</div>
						<div class="metodo-body">
							<%
								UtenteBean utenteBean = (UtenteBean) request.getSession().getAttribute("utente");
							%>
							<label for="nomeCarta">Nome Carta</label> <input type="text"
								form="aggiungi-ordine" id="nomeCarta" name="nomeCarta"
								value="<%=utenteBean.getNomeCarta()%>" disabled><br>
							<label for="cognomeCarta">Cognome Carta</label> <input type="text"
								form="aggiungi-ordine" id="cognomeCarta" name="cognomeCarta"
								value="<%=utenteBean.getNomeCarta()%>" disabled><br>
							<label for="numCarta">Numero Carta</label> <input type="text"
								form="aggiungi-ordine" id="numCarta" name="numCarta"
								value="<%=utenteBean.getNumCarta()%>" disabled><br>
							<label for="dataScadenza">Data Scadenza</label> <input
								type="date" form="aggiungi-ordine" id="dataScadenza" name="dataScadenza"
								value="<%=utenteBean.getDataScadenza()%>" disabled> <br>
							<br>

							<button type="submit" onclick="openPopUp()">Modifica
								metodo di pagamento</button>
						</div>
					</div>
					<div class="modifica-pagamento" id="modifica-pagamento">
						<div class="pagamento-header">
							<span class="header-title">Modifica Pagamento</span> <span><button
									class="close-button" onclick="closePopUp()">&times;</button></span>
						</div>
						<div class="pagamento-body">
							<form action="${pageContext.request.contextPath}/ModificaPagamento" method="POST" id="modifica-pagamento-form">
								<input type="hidden" name="modificaPagamento" value="checkout">
								<label for="nomeCartaNuova">Nome</label>
								<input type="text" id="nomeCartaNuova" name="nomeCartaNuova" required><br>
								<label for="cognomeCartaNuova">Cognome</label>
								<input type="text" id="cognomeCartaNuova" name="cognomeCartaNuova" required><br>
								<label for="numCartaNuova">Numero sulla carta </label>
								<input type="text" id="numCartaNuova" name="numCartaNuova" required><br>
								<label for="dataScadNuova">Data di scadenza</label>
								<input type="date" id="dataScadNuova" name="dataScadNuova" required><br>
								<label for="CVVNuovo">Codice sicurezza (CVV)</label>
								<input type="text" id="CVVNuovo" name="CVVNuovo" required><br>
								<button type="submit">Aggiungi carta</button>
								<div class="non-valido"></div>
							</form>
						</div>
					</div>
					<div id="overlay"></div>
					<div class="indirizzo-spedizione">
						<div class="indirizzo-header">
							<h3>Indirizzo di spedizione:</h3>
						</div>
						<div class="indirizzo-body">
							<label for="nome-spedizione">Nome </label>
							<input type="text" form="aggiungi-ordine" id="nome-spedizione" name="nome-spedizione" required><br>
							<label for="cognome-spedizione">Cognome</label>
							<input type="text" form="aggiungi-ordine" id="cognome-spedizione" name="cognome-spedizione" required><br>
							<label for="via-spedizione">Via </label>
							<input type="text" form="aggiungi-ordine" id="via-spedizione" name="via-spedizione" required> <br>
							<label for="cap-spedizione">CAP </label>
							<input type="text" form="aggiungi-ordine" id="cap-spedizione" name="cap-spedizione" required><br>
							<label for="citta-spedizione">Citt&agrave;</label>
							<input type="text" form="aggiungi-ordine" id="citta-spedizione" name="citta-spedizione" required><br>
						</div>
						<div class="non-valida"></div>
					</div>
				</div>
			</td>
			<td id="Descrizione">
				<div class="riepilogo-ordine">
					<table>
						<caption hidden>Carrello</caption>
						<tr id="element">
							<th>Nome</th>
							<th>Prezzo</th>
							<th>IVA</th>
							<th>Colore</th>
							<th>Tipo</th>
							<th>Grafica</th>
							<th>Quantita</th>
							<th>Prezzo totale</th>
						</tr>
						<%
							DecimalFormat df = new DecimalFormat("#.##");
							df.setRoundingMode(RoundingMode.FLOOR);

							for (Object o : oggettiCarrello) {
								MagliettaOrdine magliettaOrdine = (MagliettaOrdine) o;
								String prezzo = df.format(magliettaOrdine.getMagliettaBean().getPrezzo());

								if (prezzo.matches("[0-9]+"))
									prezzo += ".00";
						%>
						<tr class="prodotti-carrello" id="prodotti-carrello">
							<td class="tdt"><%=magliettaOrdine.getMagliettaBean().getNome()%>
							</td>
							<td class="tdt">&euro;&nbsp;<%=prezzo%>
							</td>
							<td class="tdt"><%=magliettaOrdine.getMagliettaBean().getIVA()%>
							</td>
							<td class="tdt"><%=magliettaOrdine.getMagliettaBean().getColore()%>
							</td>
							<td class="tdt"><%=magliettaOrdine.getMagliettaBean().getTipo()%>
							</td>
							<td class="td"><img class="immagine-prodotto"
								src="../<%=magliettaOrdine.getMagliettaBean().getGrafica()%>"
								alt="<%=magliettaOrdine.getMagliettaBean().getNome()%>"></td>
							<td class="tdt"><%=magliettaOrdine.getQuantita()%></td>
							<td class="tdt"><%=magliettaOrdine.getPrezzoTotale()%></td>
							<%
								prezzoTot += magliettaOrdine.getPrezzoTotale();
							%>
						</tr>
						<%
							}
						%>
					</table>
					<p>
						Prezzo totale:
						<%=prezzoTot%>
					<p>
				</div>
			</td>
		</tr>
	</table>
	<div class="checkout">
		<form id="aggiungi-ordine" action="${pageContext.request.contextPath}/Checkout" method="POST">
			<input type="hidden" id="data-consegna" name="data-consegna" value="<%=prima%>">
			<input type="hidden" id="prezzo-totale" name="prezzo-totale" value="<%=prezzoTot%>">
			<button type="submit" class="checkout-button">Acquista ora</button>
		</form>
	</div>
	<script src="${pageContext.request.contextPath}/js/metodoPagamento.js"></script>
	<script src="${pageContext.request.contextPath}/js/regexCheckoutIndirizzo.js"></script>
	<script src="${pageContext.request.contextPath}/js/regexCheckoutMetodoPagamento.js"></script>

	<%@ include file="footer.jsp"%>
</body>
</html>