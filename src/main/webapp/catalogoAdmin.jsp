<%@ page import="java.util.Collection" %>
<%@ page import="java.math.RoundingMode" %>
<%@ page import="java.text.DecimalFormat" %>
<%@ page import="model.maglietta.MagliettaBean" %>

<% Collection<?> magliette = (Collection<?>) request.getAttribute("magliette");
  if (magliette == null)
    response.sendRedirect("./Catalogo");
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
 // Formatter per il prezzo
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
		          			<button class="btn-shine" type="submit">
	    						<span>Mostra Descrizione</span>
                                <script src="https://cdn.lordicon.com/bhenfmcm.js" integrity="sha384-VY539ll5TIagHE4WlmKaJKJ4gKxfKtGxK0MgVqVuFG4RXvATOK4KWfapoPR/PE9K" crossorigin="anonymous"></script>
								<lord-icon src="https://cdn.lordicon.com/msoeawqm.json" trigger="hover" colors="primary:#1663c7,secondary:#f24c00" stroke="120"></lord-icon>
							</button>
		        		</form>
		    		</td>
	    		</tr>
	    		<tr>
		    		<td class="funzioni">
		        		<p style="font-size:2%">&nbsp;</p>
				        <form action="ModificaMaglietta" method="GET">
				          <input type="hidden" name="id" value="<%= maglietta.getID() %>">
				          <button class="green-btn-shine" type="submit">
	    						<span>Modifica</span>
                                <script src="https://cdn.lordicon.com/bhenfmcm.js" integrity="sha384-VY539ll5TIagHE4WlmKaJKJ4gKxfKtGxK0MgVqVuFG4RXvATOK4KWfapoPR/PE9K" crossorigin="anonymous"></script>
								<lord-icon src="https://cdn.lordicon.com/sbiheqdr.json" trigger="hover" colors="primary:#0c8125,secondary:#f24c00" stroke="120"></lord-icon>
							</button>
				        </form>
				    </td>
				    <td class="funzioni">
				        <p style="font-size:2%">&nbsp;</p>
				        <form action="DeleteMaglietta" method="POST">
				          <input type="hidden" name="ID" value="<%= maglietta.getID() %>">
				          <input type="hidden" name="tipo" value="<%= maglietta.getTipo()%>">
				          <button class="red-btn-shine" type="submit">
	    						<span>Elimina</span>
                                <script src="https://cdn.lordicon.com/bhenfmcm.js" integrity="sha384-VY539ll5TIagHE4WlmKaJKJ4gKxfKtGxK0MgVqVuFG4RXvATOK4KWfapoPR/PE9K" crossorigin="anonymous"></script>
								<lord-icon src="https://cdn.lordicon.com/gsqxdxog.json" trigger="hover" colors="primary:#810c0c,secondary:#f24c00" stroke="120"></lord-icon>
							</button>
				        </form>
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
 <br><br>


  <h1>Inserimento magliette</h1>

  <form action="SaveMaglietta" method="post" enctype="multipart/form-data">
	  <fieldset>
		  <legend>Compilare i seguenti campi</legend>
		  <label>Nome: <input type="text" name="nome" required autocomplete="off"></label> <br>
		  <label>Prezzo: <input type="text" inputmode="decimal" name="prezzo" required autocomplete="off"></label> <br>
		  <label>IVA: <input type="text" inputmode="numeric" name="IVA" required autocomplete="off"></label> <br>

		  <label for="colore">Colore: </label>
		  <select name="colore" id="colore">
			  <option value="Blu">Blu</option>
			  <option value="Rosso">Rosso</option>
			  <option value="Giallo">Giallo</option>
			  <option value="Verde">Verde</option>
			  <option value="Viola">Viola</option>
			  <option value="Rosa">Rosa</option>
			  <option value="Azzurro">Azzurro</option>
			  <option value="Nero">Nero</option>
			  <option value="Bianco">Bianco</option>
			  <option value="Arancione">Arancione</option>
		  </select> <br>

		  <label for="tipo">Tipo:</label>
		  <select name="tipo" id="tipo">
			  <option value="Anime e Manga">Anime e Manga</option>
			  <option value="Film e Serie TV">Film e Serie TV</option>
			  <option value="Girl Power">GRLPWR: Girl Power</option>
			  <option value="Fumetti">Fumetti</option>
		  </select> <br>
		  <label for="taglia">Taglia:</label>
		  <select name="taglia" id="taglia">
			  <option value="XS">XS</option>
			  <option value="S">S</option>
			  <option value="M" selected>M</option>
			  <option value="L">L</option>
			  <option value="XL">XL</option>
			  <option value="XXL">XXL</option>
		  </select> <br>
		  <label>Quantit&agrave: <input type="number" min="1" max="100" name="quantita" required autocomplete="off"></label> <br>

		  <label>Descrizione: <br> <textarea name="descrizione" required autocomplete="off"></textarea></label> <br> <br>
		  <label>Grafica: <input type="file" name="grafica" accept="image/*" required></label> <br>
		  <input type="submit" value="Carica">
	  </fieldset>
  </form>

  <script src="${pageContext.request.contextPath}/js/regexUpdateAggiuntaMaglietta.js"></script>
  <%@ include file="pages/footer.jsp" %>
</body>

</html>