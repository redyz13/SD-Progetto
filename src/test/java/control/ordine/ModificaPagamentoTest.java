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
import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

class ModificaPagamentoTest {

    private ModificaPagamento servlet;

    private HttpServletRequest req;
    private HttpServletResponse resp;
    private HttpSession session;

    private RequestDispatcher dispatcher;

    private UtenteBean utente;

    @BeforeEach
    void setup() {
        servlet = new ModificaPagamento();

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

    // {param_validi, modificaPagamento_profilo, db_ok, redirect_storico}
    @Test
    void doPost_ok_modificaProfilo_redirectStorico() throws Exception {
        when(req.getParameter("nomeCartaNuova")).thenReturn("Mario");
        when(req.getParameter("cognomeCartaNuova")).thenReturn("Rossi");
        when(req.getParameter("numCartaNuova")).thenReturn("1111");
        when(req.getParameter("dataScadNuova")).thenReturn("2030-01-01");
        when(req.getParameter("CVVNuovo")).thenReturn("999");
        when(req.getParameter("modificaPagamento")).thenReturn("profilo");

        try (MockedConstruction<UtenteDAO> utenteCons = mockConstruction(UtenteDAO.class, (mock, ctx) -> {
            doAnswer(inv -> {
                UtenteBean passed = inv.getArgument(0);

                assertEquals("Mario", passed.getNomeCarta());
                assertEquals("Rossi", passed.getCognomeCarta());
                assertEquals("1111", passed.getNumCarta());
                assertEquals(LocalDate.of(2030, 1, 1), passed.getDataScadenza());
                assertEquals("999", passed.getCVV());

                return null;
            }).when(mock).doUpdate(any(UtenteBean.class));
        })) {

            servlet.doPost(req, resp);

            UtenteDAO utenteDAO = utenteCons.constructed().get(0);
            verify(utenteDAO).doUpdate(any(UtenteBean.class));

            assertEquals("Mario", utente.getNomeCarta());
            assertEquals("Rossi", utente.getCognomeCarta());
            assertEquals("1111", utente.getNumCarta());
            assertEquals(LocalDate.of(2030, 1, 1), utente.getDataScadenza());
            assertEquals("999", utente.getCVV());

            verify(resp).sendRedirect("StoricoOrdini");
            verify(resp, never()).sendRedirect("pages/checkout.jsp");
            verify(dispatcher, never()).forward(req, resp);
        }
    }

    // {param_validi, modificaPagamento_checkout, db_ok, redirect_checkout}
    @Test
    void doPost_ok_modificaCheckout_redirectCheckout() throws Exception {
        when(req.getParameter("nomeCartaNuova")).thenReturn("Mario");
        when(req.getParameter("cognomeCartaNuova")).thenReturn("Rossi");
        when(req.getParameter("numCartaNuova")).thenReturn("1111");
        when(req.getParameter("dataScadNuova")).thenReturn("2030-01-01");
        when(req.getParameter("CVVNuovo")).thenReturn("999");
        when(req.getParameter("modificaPagamento")).thenReturn("checkout");

        try (MockedConstruction<UtenteDAO> utenteCons = mockConstruction(UtenteDAO.class, (mock, ctx) -> {
            doNothing().when(mock).doUpdate(any(UtenteBean.class));
        })) {

            servlet.doPost(req, resp);

            UtenteDAO utenteDAO = utenteCons.constructed().get(0);
            verify(utenteDAO).doUpdate(any(UtenteBean.class));

            verify(resp).sendRedirect("pages/checkout.jsp");
            verify(resp, never()).sendRedirect("StoricoOrdini");
            verify(dispatcher, never()).forward(req, resp);
        }
    }

    // {param_validi, modificaPagamento_altro, db_ok, no_redirect}
    @Test
    void doPost_ok_modificaAltro_noRedirect() throws Exception {
        when(req.getParameter("nomeCartaNuova")).thenReturn("Mario");
        when(req.getParameter("cognomeCartaNuova")).thenReturn("Rossi");
        when(req.getParameter("numCartaNuova")).thenReturn("1111");
        when(req.getParameter("dataScadNuova")).thenReturn("2030-01-01");
        when(req.getParameter("CVVNuovo")).thenReturn("999");
        when(req.getParameter("modificaPagamento")).thenReturn("altro");

        try (MockedConstruction<UtenteDAO> utenteCons = mockConstruction(UtenteDAO.class, (mock, ctx) -> {
            doNothing().when(mock).doUpdate(any(UtenteBean.class));
        })) {

            servlet.doPost(req, resp);

            UtenteDAO utenteDAO = utenteCons.constructed().get(0);
            verify(utenteDAO).doUpdate(any(UtenteBean.class));

            verify(resp, never()).sendRedirect(anyString());
            verify(dispatcher, never()).forward(req, resp);
        }
    }

    // {param_validi, db_exception, forward_error, redirect_storico}
    @Test
    void doPost_dbException_forwardErrorPage_thenRedirectStorico() throws Exception {
        when(req.getParameter("nomeCartaNuova")).thenReturn("Mario");
        when(req.getParameter("cognomeCartaNuova")).thenReturn("Rossi");
        when(req.getParameter("numCartaNuova")).thenReturn("1111");
        when(req.getParameter("dataScadNuova")).thenReturn("2030-01-01");
        when(req.getParameter("CVVNuovo")).thenReturn("999");
        when(req.getParameter("modificaPagamento")).thenReturn("profilo");

        try (MockedConstruction<UtenteDAO> utenteCons = mockConstruction(UtenteDAO.class, (mock, ctx) -> {
            doThrow(new SQLException("fail")).when(mock).doUpdate(any(UtenteBean.class));
        })) {

            servlet.doPost(req, resp);

            verify(dispatcher).forward(req, resp);
            verify(resp, never()).sendRedirect(anyString());
        }
    }

    // {param_validi, db_exception, modificaPagamento_checkout, forward_error, redirect_checkout}
    @Test
    void doPost_dbException_modificaCheckout_forwardError_thenRedirectCheckout() throws Exception {
        when(req.getParameter("nomeCartaNuova")).thenReturn("Mario");
        when(req.getParameter("cognomeCartaNuova")).thenReturn("Rossi");
        when(req.getParameter("numCartaNuova")).thenReturn("1111");
        when(req.getParameter("dataScadNuova")).thenReturn("2030-01-01");
        when(req.getParameter("CVVNuovo")).thenReturn("999");
        when(req.getParameter("modificaPagamento")).thenReturn("checkout");

        try (MockedConstruction<UtenteDAO> utenteCons = mockConstruction(UtenteDAO.class, (mock, ctx) -> {
            doThrow(new SQLException("fail")).when(mock).doUpdate(any(UtenteBean.class));
        })) {

            servlet.doPost(req, resp);

            verify(dispatcher).forward(req, resp);
            verify(resp, never()).sendRedirect(anyString());
        }
    }

    // -------- Test doGet() --------

    // {delegazione_a_doPost}
    @Test
    void doGet_delegaDoPost() throws Exception {
        when(req.getParameter("nomeCartaNuova")).thenReturn("Mario");
        when(req.getParameter("cognomeCartaNuova")).thenReturn("Rossi");
        when(req.getParameter("numCartaNuova")).thenReturn("1111");
        when(req.getParameter("dataScadNuova")).thenReturn("2030-01-01");
        when(req.getParameter("CVVNuovo")).thenReturn("999");
        when(req.getParameter("modificaPagamento")).thenReturn("checkout");

        try (MockedConstruction<UtenteDAO> utenteCons = mockConstruction(UtenteDAO.class, (mock, ctx) -> {
            doNothing().when(mock).doUpdate(any(UtenteBean.class));
        })) {

            servlet.doGet(req, resp);

            UtenteDAO utenteDAO = utenteCons.constructed().get(0);
            verify(utenteDAO).doUpdate(any(UtenteBean.class));

            verify(resp).sendRedirect("pages/checkout.jsp");
            verify(dispatcher, never()).forward(req, resp);
        }
    }
}
