package control.ordine;

import model.utente.UtenteBean;
import model.utente.UtenteDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import javax.servlet.RequestDispatcher;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

class ModificaIndirizzoTest {

    private ModificaIndirizzo servlet;

    private HttpServletRequest req;
    private HttpServletResponse resp;
    private HttpSession session;

    private RequestDispatcher dispatcher;

    private UtenteBean utente;

    @BeforeEach
    void setup() {
        servlet = new ModificaIndirizzo();

        req = mock(HttpServletRequest.class);
        resp = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);

        dispatcher = mock(RequestDispatcher.class);

        utente = new UtenteBean();

        when(req.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utente);

        when(req.getRequestDispatcher("/pages/errorpage.jsp")).thenReturn(dispatcher);
    }

    // -------- Test doPost() --------

    // {param_validi, db_ok, redirect_storico}
    @Test
    void doPost_ok_updatesBeanAndRedirects() throws Exception {
        when(req.getParameter("viaNuova")).thenReturn("Via Mango");
        when(req.getParameter("cittaNuova")).thenReturn("Casotto");
        when(req.getParameter("capNuova")).thenReturn("80000");

        try (MockedConstruction<UtenteDAO> utenteCons = mockConstruction(UtenteDAO.class, (mock, ctx) -> {
            doAnswer(inv -> {
                UtenteBean passed = inv.getArgument(0);

                assertEquals("Via Mango", passed.getVia());
                assertEquals("Casotto", passed.getCitta());
                assertEquals("80000", passed.getCap());

                return null;
            }).when(mock).doUpdate(any(UtenteBean.class));
        })) {

            servlet.doPost(req, resp);

            UtenteDAO utenteDAO = utenteCons.constructed().get(0);
            verify(utenteDAO).doUpdate(any(UtenteBean.class));

            assertEquals("Via Mango", utente.getVia());
            assertEquals("Casotto", utente.getCitta());
            assertEquals("80000", utente.getCap());

            verify(resp).sendRedirect("StoricoOrdini");
            verify(dispatcher, never()).forward(req, resp);
        }
    }

    // {param_validi, db_exception, forward_error, redirect_called}
    @Test
    void doPost_dbException_forwardsError_thenRedirects() throws Exception {
        when(req.getParameter("viaNuova")).thenReturn("Via Mango");
        when(req.getParameter("cittaNuova")).thenReturn("Casotto");
        when(req.getParameter("capNuova")).thenReturn("80000");

        try (MockedConstruction<UtenteDAO> utenteCons = mockConstruction(UtenteDAO.class, (mock, ctx) -> {
            doThrow(new SQLException("fail")).when(mock).doUpdate(any(UtenteBean.class));
        })) {

            servlet.doPost(req, resp);

            verify(dispatcher).forward(req, resp);
            verify(resp).sendRedirect("StoricoOrdini");
        }
    }
}
