<%@ page import="model.maglietta.MagliettaOrdine" %>
<%@ page import="java.text.DecimalFormat" %>
<%@ page import="java.math.RoundingMode" %>
<%@ page import="java.util.Collection" %>
<%@ page import="model.CarrelloModel" %>

<%
  CarrelloModel carrello;
  synchronized (session) {
    carrello = (CarrelloModel) session.getAttribute("carrello");
    if (carrello == null) {
      carrello = new CarrelloModel();
      session.setAttribute("carrello", carrello);
    }
  }

  Collection<?> oggettiCarrello = carrello.getCarrello();
%>

<!DOCTYPE html>
<html lang="it">

<head>
  <meta charset="UTF-8">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  
<link rel="stylesheet"
	href="${pageContext.request.contextPath}/css/carrello.css">
  <title>Carrello</title>
</head>
<body>
<%@ include file="header.jsp" %>
<h1>Carrello</h1>
<table id="prodotti">
  <caption hidden>Carrello</caption>
  <tr id="element" hidden>
    <th>Nome</th>
    <th>Prezzo</th>
    <th>IVA</th>
    <th>Colore</th>
    <th>Tipo</th>
    <th>Grafica</th>
    <th>Taglia</th>
    <th>Quantit&#224</th>
  </tr>
  <tr>
  	<td>Nome</td>
  	<td>Prezzo</td>
  	<td>Iva</td>
  	<td>Colore</td>
  	<td>Tipo</td>
  	<td>Grafica</td>
  	<td>Taglia</td>
  	<td>Quantit&#224</td>
  </tr>
  <%
  	int si = 0;
    if (oggettiCarrello != null && oggettiCarrello.size() != 0) {
      si = 1;
      DecimalFormat df = new DecimalFormat("#.##");
      df.setRoundingMode(RoundingMode.FLOOR);

      for (Object o : oggettiCarrello) {
        MagliettaOrdine magliettaOrdine = (MagliettaOrdine) o;
        String prezzo = df.format(magliettaOrdine.getMagliettaBean().getPrezzo());

        if (prezzo.matches("[0-9]+"))
          prezzo += ".00";
  %>
  <tr class="productRow" id="<%= magliettaOrdine.getMagliettaBean().getID() + magliettaOrdine.getTaglia() %>">
    <td><%= magliettaOrdine.getMagliettaBean().getNome() %> </td>
    <td>&euro;&nbsp;<%= prezzo %> </td>
    <td><%= magliettaOrdine.getMagliettaBean().getIVA() %> </td>
    <td><%= magliettaOrdine.getMagliettaBean().getColore() %> </td>
    <td><%= magliettaOrdine.getMagliettaBean().getTipo() %> </td>
    <td><img src="../<%= magliettaOrdine.getMagliettaBean().getGrafica() %>" alt="<%= magliettaOrdine.getMagliettaBean().getNome() %>" class="img-cart"></td>
    <td><%= magliettaOrdine.getTaglia() %> </td>
    <td>
      <form class="addForm">
        <label>
        <input type="number" name="quantita" min="0" max="100" value="<%= magliettaOrdine.getQuantita() %>" class="inputQuan">
        <input type="hidden" name="ID" value="<%= magliettaOrdine.getMagliettaBean().getID() %>">
        <input type="hidden" name="taglia" value="<%= magliettaOrdine.getTaglia() %>">
        <br><br>
        <button type="submit" class="button2">Aggiorna</button>
        </label>
      </form>
    </td>
    <td>
      <form class="rmvForm">
        <input type="hidden" name="ID" value="<%= magliettaOrdine.getMagliettaBean().getID() %>">
        <input type="hidden" name="taglia" value="<%= magliettaOrdine.getTaglia() %>">
        <button type="submit" class="button22">Elimina</button>
      </form>
    </td>
  </tr>
  <%
      // Parentesi del for e dell'if
  } } else {
  %>
  <tr>
    <td colspan="7">Nessun prodotto nel carrello</td>
  </tr>
  <% } %>
</table>
<% if (si > 0) %>
	<div id="checkout">
    <form action="${pageContext.request.contextPath}/CheckoutRedirect" method="POST">
      <button type="submit" class="button222">Checkout</button>
    </form>
  </div>
<%@ include file="footer.jsp" %>

<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.6.4/jquery.min.js" integrity="sha384-UG8ao2jwOWB7/oDdObZc6ItJmwUkR/PfMyt9Qs5AwX7PsnYn1CRKCTWyncPTWvaS" crossorigin="anonymous"></script>
<script type="text/javascript">
  $(document).ready(function() {
    $(".addForm").on("submit", function(event) {
      event.preventDefault();
      $.ajax({
        type: "POST",
        url: "${pageContext.request.contextPath}/AggiungiMaglietta",
        data: $(this).serialize()
      });
    });
    $(".rmvForm").on("submit", function(event) {
      event.preventDefault();
      $.ajax({
        type: "POST",
        url: "${pageContext.request.contextPath}/RimuoviMaglietta",
        data: $(this).serialize(),
        success: function() {
          let ID = $(".rmvForm input[name='ID']").attr("value");
          let taglia = $(".rmvForm input[name='taglia']").attr("value");
          document.getElementById(ID.toString() + taglia).remove();

          if (document.getElementsByClassName("productRow").length === 0)
            location.reload();
        }
      });
    });
  });
</script>

</body>
