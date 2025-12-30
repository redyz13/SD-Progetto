package control.ordine;
import model.CarrelloModel;
import model.acquisto.AcquistoBean;
import model.acquisto.AcquistoDAO;
import model.maglietta.MagliettaOrdine;
import model.misura.MisuraDAO;
import model.ordine.OrdineBean;
import model.ordine.OrdineDAO;
import model.utente.UtenteBean;

import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.sql.SQLException;
import java.time.LocalDate;

@WebServlet("/Checkout")
public class Checkout extends HttpServlet {
    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        final String ERROR_PAGE = "/pages/errorpage.jsp";
        CarrelloModel carrelloModel = (CarrelloModel) req.getSession().getAttribute("carrello");
        UtenteBean utenteBean = (UtenteBean) req.getSession().getAttribute("utente");

        LocalDate dataConsegna;
        try {
            dataConsegna = LocalDate.parse(req.getParameter("data-consegna"));
        } catch (java.time.format.DateTimeParseException | NullPointerException e) {
            req.getRequestDispatcher(ERROR_PAGE).forward(req, resp);
            return;
        }

        float prezzoTot;
        try {
            prezzoTot = Float.parseFloat(req.getParameter("prezzo-totale"));
        } catch (NumberFormatException | NullPointerException e) {
            req.getRequestDispatcher(ERROR_PAGE).forward(req, resp);
            return;
        }

        OrdineBean ordineBean = new OrdineBean();
        ordineBean.setUsername(utenteBean.getUsername());
        ordineBean.setPrezzoTotale(prezzoTot);
        ordineBean.setDataConsegna(dataConsegna);
        ordineBean.setDataOrdine(LocalDate.now());
        ordineBean.setNomeConsegna(req.getParameter("nome-spedizione"));
        ordineBean.setCognomeConsegna(req.getParameter("cognome-spedizione"));
        ordineBean.setCap(req.getParameter("cap-spedizione"));
        ordineBean.setVia(req.getParameter("via-spedizione"));
        ordineBean.setCitta(req.getParameter("citta-spedizione"));
        OrdineDAO ordineDAO = new OrdineDAO();

        try {
            ordineDAO.doSave(ordineBean);
        } catch (SQLException e) {
            req.getRequestDispatcher(ERROR_PAGE).forward(req, resp);
        }

        for (MagliettaOrdine p: carrelloModel.getCarrello()) {
            try {
                AcquistoBean acquistoBean = new AcquistoBean();
                acquistoBean.setIDOrdine(new OrdineDAO().getMaxID() - 1);
                acquistoBean.setIDMaglietta(p.getMagliettaBean().getID());
                acquistoBean.setQuantita(p.getQuantita());
                acquistoBean.setImmagine(p.getMagliettaBean().getGrafica());
                acquistoBean.setPrezzoAq(p.getMagliettaBean().getPrezzo());
                acquistoBean.setIvaAq(p.getMagliettaBean().getIVA());
                acquistoBean.setTaglia(p.getTaglia());

                AcquistoDAO acquistoDAO = new AcquistoDAO();
                acquistoDAO.doSave(acquistoBean);

                MisuraDAO misuraDAO = new MisuraDAO();
                misuraDAO.doUpdateUtente(acquistoBean, p.getTaglia());

            } catch (SQLException e) {
                req.getRequestDispatcher(ERROR_PAGE).forward(req, resp);
            }
        }

        req.getSession().removeAttribute("carrello");

        resp.sendRedirect("pages/acquisto.jsp");
    }
}
