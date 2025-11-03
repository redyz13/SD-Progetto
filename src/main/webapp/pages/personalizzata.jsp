<!DOCTYPE html>
<html lang="it">
	<head>
		<meta charset="UTF-8">
		<meta http-equiv="X-UA-Compatible" content="IE=edge">
		<meta name="viewport" content="width=device-width, initial-scale=1.0">
		<link rel="stylesheet" href="${pageContext.request.contextPath}/css/personalizzata.css">
        <title>Personalizza maglietta</title>
	</head>
	<body>
		<%@ include file="header.jsp"%>

        <form method="POST" id="form" action="${pageContext.request.contextPath}/SaveCustom"></form>
        <input form="form" type="hidden" id="imgData" name="imgData">

		<script src="${pageContext.request.contextPath}/js/personalizzata.js"></script>
		<div class="container">
	        <div class="tshirt-div" id="tshirt">
	            <img id="tshirt-backgroundpicture" src="${pageContext.request.contextPath}/images/system/tshirt-base.png" alt="T-shirt background"/>
	            <img id="tshirt-new" src="${pageContext.request.contextPath}/images/system/void.png" alt="Nuova T-Shirt">
	        </div>
	        <br>
	        <div clas="text-container">
	        <br><br><br><br>
		        <label for="tshirt-design" class="Label">Grafica T-Shirt:</label>
		        <select id="tshirt-design" onchange="addImage()">
		            <option value="">Seleziona uno dei nostri design ...</option>
		            <option value="${pageContext.request.contextPath}/images/system/logo.png">whiTee</option>
		        </select>
		        <br><br>
		        <label for="tshirt-color" class="Label">Colore T-Shirt:</label>
		        <select name="colore" form="form" id="tshirt-color" onchange="changeColor()">
		            <option value="Viola">Viola</option>
		            <option value="Bianco" selected>Bianco</option>
		            <option value="Nero">Nero</option>
		            <option value="Rosso">Rosso</option>
		            <option value="Verde">Verde</option>
		        </select>
		        <br><br><label class="Label">Taglia:<select form="form" name="taglia" class="button" id="size" required>
		            <option value="XS" selected>XS</option>
		            <option value="S">S</option>
		            <option value="M">M</option>
		            <option value="L">L</option>
		            <option value="XL">XL</option>
		            <option value="XXL">XXL</option>
		        </select></label>
		        <br><br>
		        <label for="tshirt-custompicture" class="Label">Carica la tua grafica:</label>
		        <input type="file" id="tshirt-custompicture" accept="image/*" onchange="addNew()"><br><br>
		        <button class="btn-shine" onclick="saveTshirtImage()">
    						<span>Aggiungi al carrello</span>
							<script src="https://cdn.lordicon.com/bhenfmcm.js" integrity="sha384-VY539ll5TIagHE4WlmKaJKJ4gKxfKtGxK0MgVqVuFG4RXvATOK4KWfapoPR/PE9K" crossorigin="anonymous"></script>
							<lord-icon src="https://cdn.lordicon.com/dnoiydox.json" trigger="hover" colors="primary:#1663c7,secondary:#f24c00" stroke="85"></lord-icon>
				</button>
	        </div>
        </div>
        <script src="https://html2canvas.hertzen.com/dist/html2canvas.js" integrity="sha384-q0KsXOmCeCEoVzvj91Xfq+Z9A/MA9/K7PhfVXTTZHQiZ+snp/JlaXl08LNAT7mrM" crossorigin="anonymous"></script>
        <script>
              function saveTshirtImage() {
                  // Utilizza html2canvas per catturare il contenuto del div con id "tshirt"
                  html2canvas(document.getElementById("tshirt")).then(function (canvas) {
                      // Converti il canvas in un'immagine PNG e inserisci i dati dell'immagine nel campo nascosto del modulo
                      document.getElementById("imgData").value = canvas.toDataURL("image/png");

                      // Invia il modulo per salvare l'immagine sul server
                      document.getElementById("form").submit();
                  });
              }
        </script>
    <%@ include file="footer.jsp"%>
	</body>
</html>