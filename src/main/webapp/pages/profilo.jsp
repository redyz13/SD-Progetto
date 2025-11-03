<%@ page import="model.utente.UtenteBean" %>
<%@ page import="java.util.Map" %>
<%@ page import="java.util.Collection" %>
<%@ page import="model.acquisto.AcquistoBean" %>
<%@ page import="model.ordine.OrdineBean" %>
<%@ page import="java.time.format.DateTimeFormatter" %>
<%@ page import="java.time.format.FormatStyle" %>
<%@ page contentType="text/html;charset=UTF-8" %>


<% UtenteBean utenteBean = (UtenteBean) request.getSession().getAttribute("utente"); %>

<%
    Map<?, ?> ordini = (Map<?, ?>) request.getAttribute("ordini");
    if (ordini == null)
        response.sendRedirect("../StoricoOrdini");
%>
<% request.getSession().setAttribute("ordini", ordini); %>

<!DOCTYPE html>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta http-equiv="X-UA-Compatible" content="IE=edge">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Profilo utente</title>
    <link rel="stylesheet" href="${pageContext.request.contextPath}/css/modificaIndirizzo.css">
    <link rel="stylesheet" href="${pageContext.request.contextPath}/css/modificaPagamento.css">
    <link rel="stylesheet" href="${pageContext.request.contextPath}/css/profilo.css">
</head>
<body>
<%@ include file="header.jsp" %>
<div class="profilo">
    <div class="utente-header">
        <h3>Bentornato <%= utenteBean.getUsername()%>!</h3>
    </div>
    <div class="indirizzo-e-header">
        <div class="indirizzo">
            <div class="indirizzo-header">Indirizzo</div>
            <div class="indirizzo-body">
                <label for="via-utente">Via: </label>
                <input type="text" name="via-utente" id="via-utente" value="<%=utenteBean.getVia() %>" disabled>
                <label for="citta-utente">Citta: </label>
                <input type="text" name="citta-utente" id="citta-utente" value="<%=utenteBean.getCitta()%>" disabled>
                <label for="cap-utente">Cap: </label>
                <input type="text" name="cap-utente" id="cap-utente" value="<%=utenteBean.getCap()%>" disabled>
            </div>
            <div class="indirizzo-button">
                <button class="indirizzo-button button" onclick="openPopUpIndirizzo()" type="submit">Modifica indirizzo</button>
            </div>

            <div class="modifica-indirizzo" id="modifica-indirizzo">
                <div class="indirizzo-header">
                    <span class="header-title">Modifica indirizzo</span>
                    <span><button class="close-button" onclick="closePopUpIndirizzo()">&times;</button></span>
                </div>
                <div class="indirizzo-body">
                    <form action="ModificaIndirizzo" method="POST" id="modifica-indirizzo-form">
                        <label for="viaNuova">Via: </label>
                        <input type="text" id="viaNuova" name="viaNuova" required><br>
                        <label for="cittaNuova">Città: </label>
                        <input type="text"  id="cittaNuova" name="cittaNuova" required><br>
                        <label for="capNuova">Cap: </label>
                        <input type="text" id="capNuova" name="capNuova" required><br>
                        <button type="submit" class="button">Aggiungi indirizzo</button>
                        <div class="non-valido"></div>
                    </form>
                </div>
            </div>
        </div>
        <div id="overlayIndirizzo"></div>


        <div class="metodo-di-pagamento">
            <div class="pagamento-header">Metodo di Pagamento</div>
            <div class="pagamento-body-no-modifica">
                <label for="nomeCarta">Nome Carta</label><br>
                <input type="text" id="nomeCarta" name="nomeCarta" value="<%=utenteBean.getNomeCarta()%>" disabled><br><br>
                <label for="cognomeCarta">Cognome Carta</label><br>
                <input type="text" id="cognomeCarta" name="cognomeCarta" value="<%=utenteBean.getNomeCarta()%>" disabled><br><br>
                <label for="numCarta">Numero Carta</label><br>
                <input type="text" id="numCarta" name="numCarta" value="<%=utenteBean.getNumCarta()%>" disabled><br><br>
                <label for="dataScadenza">Data Scadenza</label><br>
                <input type="text" id="dataScadenza" name="dataScadenza" value="<%=utenteBean.getDataScadenza()%>" disabled><br><br>
            </div>
            <div class="pagamento-button">
                    <button class="pagamento-button button" type="submit" onclick="openPopUp()">Modifica metodo di pagamento</button>
            </div>
            <div class="modifica-pagamento" id="modifica-pagamento">
                <div class="pagamento-header">
                    <span class="header-title">Modifica pagamento</span> <span><button
                        class="close-button" onclick="closePopUp()">&times;</button></span>
                </div>
                <div class="pagamento-body">
                    <form action="ModificaPagamento" method="POST" id="modifica-pagamento-form">
                        <input type="hidden" name="modificaPagamento" value="profilo">
                        <label for="nomeCartaNuova">Nome: </label>
                        <input type="text" id="nomeCartaNuova" name="nomeCartaNuova" required><br>
                        <label for="cognomeCartaNuova">Cognome: </label>
                        <input type="text" id="cognomeCartaNuova" name="cognomeCartaNuova" required><br>
                        <label for="numCartaNuova">Numero sulla carta: </label>
                        <input type="text" id="numCartaNuova" name="numCartaNuova" required><br>
                        <label for="dataScadNuova">Data di scadenza: </label>
                        <input type="date" id="dataScadNuova" name="dataScadNuova" required><br>
                        <label for="CVVNuovo">Codice sicurezza (CVV): </label>
                        <input type="text" id="CVVNuovo" name="CVVNuovo" required><br>
                        <button type="submit" class="button">Aggiungi carta </button>
                        <div class="non-valido"></div>
                    </form>
                </div>
            </div>
            <div id="overlay"></div>
        </div>
    </div>
    <div class="ordini">
        <%
            if (ordini != null)
                for (Map.Entry<?, ?> entry : ordini.entrySet()) {
                    OrdineBean ordineBean = (OrdineBean) entry.getKey();
                    Collection<AcquistoBean> acquisti = (Collection<AcquistoBean>) entry.getValue();
        %>
        <table>
            <caption hidden>Ordini</caption>
            <tr class="header-ordini">
                <th>Ordine numero</th>
                <th>Prezzo Totale</th>
                <th>Data Ordine</th>
                <th></th>
                <th></th>
            </tr>
            <tr>
                <td><%= ordineBean.getID() %></td>
                <td>€ <%= ordineBean.getPrezzoTotale() %></td>
                <td><%=ordineBean.getDataOrdine().format(DateTimeFormatter.ofLocalizedDate(FormatStyle.SHORT))%></td>
                <td>
                    <button type="button" id="<%=ordineBean.getID()%>" class="button" onclick="slide(<%=ordineBean.getID()%>, 'tr<%=ordineBean.getID()%>')">Mostra dettagli</button>
                </td>
                <td>
                    <form method="POST" action="StampaFattura">
                        <button type="submit" class="button">Stampa fattura</button>
                        <input type="hidden" name="IDOrdine" value="<%= ordineBean.getID() %>">
                    </form>
                </td>
            </tr>

            <tr class="acquisti" id="tr<%=ordineBean.getID()%>">
                <td>
                    <table>
                        <caption hidden>Tabella acquisti</caption>
                        <%
                        for (AcquistoBean acquisto: acquisti) {
                        %>
                        <tr>
                            <th>Grafica</th>
                            <th>Quantità</th>
                            <th>Taglia</th>
                            <th>Prezzo</th>
                            <th>IVA</th>
                        </tr>
                        <tr>
                            <td>
                                <img src="<%= acquisto.getImmagine() %>" alt="<%= acquisto.getIDMaglietta() %>">
                            </td>
                            <td>
                                <p><%=acquisto.getQuantita()%></p>
                            </td>
                            <td>
                                <p><%=acquisto.getTaglia()%></p>
                            </td>
                            <td>
                                <p><%=acquisto.getPrezzoAq()%></p>
                            </td>
                            <td>
                                <p><%=acquisto.getIvaAq()%></p>
                            </td>
                        </tr>
                        <% } %>
                    </table>
                </td>
            </tr>
        </table>
        <% }%>
    </div>
</div>
<script src="${pageContext.request.contextPath}/js/metodoPagamento.js"></script>
<script src="${pageContext.request.contextPath}/js/modificaIndirizzo.js"></script>
<script>
    let toggle = false;
</script>
<script>
    function slide(ordine, acquisto) {
        toggle ^= true;

        let acq = document.getElementById(acquisto);
        let button = document.getElementById(ordine);

        if (toggle) {
            acq.classList.remove("acquisti");
            button.innerText = "Mostra meno";
        }
        else {
            acq.classList.add("acquisti");
            button.innerText = "Mostra dettagli";
        }
    }
</script>
<%@ include file="footer.jsp"%>
</body>
</html>
