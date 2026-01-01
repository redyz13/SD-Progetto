package control;

import model.acquisto.AcquistoBean;
import model.ordine.OrdineBean;
import model.utente.UtenteBean;
import org.apache.pdfbox.pdmodel.PDDocument;
import org.apache.pdfbox.pdmodel.PDPage;
import org.apache.pdfbox.pdmodel.PDPageContentStream;
import org.apache.pdfbox.pdmodel.font.PDType1Font;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;
import org.mockito.MockedStatic;
import javax.servlet.RequestDispatcher;
import javax.servlet.ServletContext;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import java.io.File;
import java.io.IOException;
import java.lang.reflect.Method;
import java.time.LocalDate;
import java.util.*;

import static org.junit.jupiter.api.Assertions.assertNull;
import static org.mockito.Mockito.*;

class StampaFatturaTest {

    private StampaFattura servlet;
    private HttpServletRequest req;
    private HttpServletResponse resp;
    private HttpSession session;
    private ServletContext context;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setup() {
        servlet = new StampaFattura();
        req = mock(HttpServletRequest.class);
        resp = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        context = mock(ServletContext.class);
        dispatcher = mock(RequestDispatcher.class);

        when(req.getSession()).thenReturn(session);
        when(req.getServletContext()).thenReturn(context);
        when(context.getRealPath("/pdf/")).thenReturn("/tmp/");
        when(req.getRequestDispatcher("/pages/errorpage.jsp")).thenReturn(dispatcher);
    }

    // -------- Test doPost() --------

    // {id_valido, ordine_trovato, pdf_ok, scrittura_pdf = effettuata}
    @Test
    void doPost_ok_pdfWritingVerified() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("1");

        UtenteBean utente = mock(UtenteBean.class);
        when(utente.getNumCarta()).thenReturn("1234");
        when(utente.getNome()).thenReturn("Mario");
        when(utente.getCognome()).thenReturn("Rossi");
        when(utente.getVia()).thenReturn("Via Mango");
        when(utente.getCap()).thenReturn("80000");
        when(utente.getCitta()).thenReturn("Casotto");

        OrdineBean ordine = mock(OrdineBean.class);
        when(ordine.getID()).thenReturn(1);
        when(ordine.getPrezzoTotale()).thenReturn(39f);
        when(ordine.getDataOrdine()).thenReturn(LocalDate.now());

        AcquistoBean acquisto1 = mock(AcquistoBean.class);
        when(acquisto1.getIDMaglietta()).thenReturn(10);
        when(acquisto1.getQuantita()).thenReturn(2);
        when(acquisto1.getPrezzoAq()).thenReturn(5f);

        AcquistoBean acquisto2 = mock(AcquistoBean.class);
        when(acquisto2.getIDMaglietta()).thenReturn(20);
        when(acquisto2.getQuantita()).thenReturn(3);
        when(acquisto2.getPrezzoAq()).thenReturn(7f);

        Map<OrdineBean, Collection<AcquistoBean>> ordini = new HashMap<>();
        ordini.put(ordine, List.of(acquisto1, acquisto2));

        when(session.getAttribute("utente")).thenReturn(utente);
        when(session.getAttribute("ordini")).thenReturn(ordini);

        PDDocument documentMock = mock(PDDocument.class);
        when(documentMock.getPage(0)).thenReturn(mock(PDPage.class));

        List<PDPageContentStream> createdStreams = new ArrayList<>();

        try (
                MockedStatic<PDDocument> mockedStatic = mockStatic(PDDocument.class);
                MockedConstruction<PDPageContentStream> mockedStream =
                        mockConstruction(PDPageContentStream.class,
                                (cs, ctx) -> createdStreams.add(cs))
        ) {
            mockedStatic.when(() -> PDDocument.load(any(File.class)))
                    .thenReturn(documentMock);

            servlet.doPost(req, resp);

            PDPageContentStream cs = createdStreams.get(0);

            verify(cs).setFont(PDType1Font.HELVETICA, 8);
            verify(cs, atLeastOnce()).beginText();
            verify(cs, atLeastOnce()).endText();

            verify(cs).newLineAtOffset(446.609f, 767.3385f);
            verify(cs).showText("1234");

            verify(cs).newLineAtOffset(46.6203f, 642.2537f);
            verify(cs).showText("Mario");

            verify(cs).newLineAtOffset(46.6203f, 631.2537f);
            verify(cs).showText("Rossi");

            verify(cs).newLineAtOffset(46.6203f, 620.2537f);
            verify(cs).showText("Via Mango 80000");

            verify(cs).newLineAtOffset(46.6203f, 609.2537f);
            verify(cs).showText("Casotto");

            verify(cs).newLineAtOffset(405.1517f, 591.2341f);
            verify(cs).showText("39.0 euro");

            verify(cs).newLineAtOffset(92.7409f, 448.0316f);
            verify(cs).showText("10");

            verify(cs).newLineAtOffset(288.2813f, 448.0316f);
            verify(cs).showText("2");

            verify(cs).newLineAtOffset(344.4793f, 448.0316f);
            verify(cs).showText("5.0 euro");

            verify(cs).newLineAtOffset(515.6068f, 448.0316f);
            verify(cs).showText("10.0 euro");

            verify(cs).newLineAtOffset(92.7409f, 433.0316f);
            verify(cs).showText("20");

            verify(cs).newLineAtOffset(288.2813f, 433.0316f);
            verify(cs).showText("3");

            verify(cs).newLineAtOffset(344.4793f, 433.0316f);
            verify(cs).showText("7.0 euro");

            verify(cs).newLineAtOffset(515.6068f, 433.0316f);
            verify(cs).showText("21.0 euro");

            verify(cs).close();
            verify(documentMock).close();
            verify(resp).setContentType("application/pdf");
            verify(resp).setCharacterEncoding("UTF-8");
            verify(resp).setHeader("Content-Disposition", "attachment; filename=output.pdf");
            verify(resp).sendRedirect("pdf/output.pdf");
            verify(dispatcher, never()).forward(req, resp);
        }
    }

    // {id_valido, ordine_trovato, pdf_ok, begin_end_text_required}
    @Test
    void doPost_ok_beginEndTextRequired() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("1");

        UtenteBean utente = mock(UtenteBean.class);
        when(utente.getNumCarta()).thenReturn("1234");
        when(utente.getNome()).thenReturn("Mario");
        when(utente.getCognome()).thenReturn("Rossi");
        when(utente.getVia()).thenReturn("Via Mango");
        when(utente.getCap()).thenReturn("80000");
        when(utente.getCitta()).thenReturn("Casotto");

        OrdineBean ordine = mock(OrdineBean.class);
        when(ordine.getID()).thenReturn(1);
        when(ordine.getPrezzoTotale()).thenReturn(39f);
        when(ordine.getDataOrdine()).thenReturn(LocalDate.now());

        AcquistoBean acquisto = mock(AcquistoBean.class);
        when(acquisto.getIDMaglietta()).thenReturn(10);
        when(acquisto.getQuantita()).thenReturn(2);
        when(acquisto.getPrezzoAq()).thenReturn(5f);

        Map<OrdineBean, Collection<AcquistoBean>> ordini = new HashMap<>();
        ordini.put(ordine, List.of(acquisto));

        when(session.getAttribute("utente")).thenReturn(utente);
        when(session.getAttribute("ordini")).thenReturn(ordini);

        PDDocument documentMock = mock(PDDocument.class);
        when(documentMock.getPage(0)).thenReturn(mock(PDPage.class));
        doNothing().when(documentMock).save(any(File.class));

        List<PDPageContentStream> createdStreams = new ArrayList<>();

        try (
                MockedStatic<PDDocument> mockedStatic = mockStatic(PDDocument.class);
                MockedConstruction<PDPageContentStream> mockedStream =
                        mockConstruction(PDPageContentStream.class,
                                (cs, ctx) -> {
                                    createdStreams.add(cs);

                                    java.util.concurrent.atomic.AtomicBoolean inText =
                                            new java.util.concurrent.atomic.AtomicBoolean(false);

                                    doAnswer(inv -> { inText.set(true); return null; }).when(cs).beginText();
                                    doAnswer(inv -> { inText.set(false); return null; }).when(cs).endText();

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("showText outside beginText/endText");
                                        return null;
                                    }).when(cs).showText(anyString());

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("newLineAtOffset outside beginText/endText");
                                        return null;
                                    }).when(cs).newLineAtOffset(anyFloat(), anyFloat());

                                    doAnswer(inv -> {
                                        if (inText.get()) throw new IOException("close while text still open");
                                        return null;
                                    }).when(cs).close();
                                })
        ) {
            mockedStatic.when(() -> PDDocument.load(any(File.class)))
                    .thenReturn(documentMock);

            servlet.doPost(req, resp);

            verify(resp).setContentType("application/pdf");
            verify(resp).setCharacterEncoding("UTF-8");
            verify(resp).setHeader("Content-Disposition", "attachment; filename=output.pdf");
            verify(resp).sendRedirect("pdf/output.pdf");
            verify(dispatcher, never()).forward(req, resp);

            PDPageContentStream cs = createdStreams.get(0);
            verify(cs, atLeastOnce()).beginText();
            verify(cs, atLeastOnce()).endText();
            verify(cs).close();
            verify(documentMock).close();
        }
    }

    // {id_valido, ordine_trovato, pdf_ok, endText_last_before_close}
    @Test
    void doPost_ok_endTextLastBeforeClose() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("1");

        UtenteBean utente = mock(UtenteBean.class);
        when(utente.getNumCarta()).thenReturn("1234");
        when(utente.getNome()).thenReturn("Mario");
        when(utente.getCognome()).thenReturn("Rossi");
        when(utente.getVia()).thenReturn("Via Mango");
        when(utente.getCap()).thenReturn("80000");
        when(utente.getCitta()).thenReturn("Casotto");

        OrdineBean ordine = mock(OrdineBean.class);
        when(ordine.getID()).thenReturn(1);
        when(ordine.getPrezzoTotale()).thenReturn(39f);
        when(ordine.getDataOrdine()).thenReturn(LocalDate.now());

        AcquistoBean acquisto = mock(AcquistoBean.class);
        when(acquisto.getIDMaglietta()).thenReturn(10);
        when(acquisto.getQuantita()).thenReturn(2);
        when(acquisto.getPrezzoAq()).thenReturn(5f);

        Map<OrdineBean, Collection<AcquistoBean>> ordini = new HashMap<>();
        ordini.put(ordine, List.of(acquisto));

        when(session.getAttribute("utente")).thenReturn(utente);
        when(session.getAttribute("ordini")).thenReturn(ordini);

        PDDocument documentMock = mock(PDDocument.class);
        when(documentMock.getPage(0)).thenReturn(mock(PDPage.class));
        doNothing().when(documentMock).save(any(File.class));

        List<PDPageContentStream> createdStreams = new ArrayList<>();

        try (
                MockedStatic<PDDocument> mockedStatic = mockStatic(PDDocument.class);
                MockedConstruction<PDPageContentStream> mockedStream =
                        mockConstruction(PDPageContentStream.class,
                                (cs, ctx) -> {
                                    createdStreams.add(cs);

                                    java.util.concurrent.atomic.AtomicBoolean inText =
                                            new java.util.concurrent.atomic.AtomicBoolean(false);
                                    java.util.concurrent.atomic.AtomicBoolean lastWasEndText =
                                            new java.util.concurrent.atomic.AtomicBoolean(false);

                                    doAnswer(inv -> {
                                        if (inText.get()) throw new IllegalStateException("nested beginText");
                                        inText.set(true);
                                        lastWasEndText.set(false);
                                        return null;
                                    }).when(cs).beginText();

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("endText without beginText");
                                        inText.set(false);
                                        lastWasEndText.set(true);
                                        return null;
                                    }).when(cs).endText();

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("newLineAtOffset outside beginText/endText");
                                        lastWasEndText.set(false);
                                        return null;
                                    }).when(cs).newLineAtOffset(anyFloat(), anyFloat());

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("showText outside beginText/endText");
                                        lastWasEndText.set(false);
                                        return null;
                                    }).when(cs).showText(anyString());

                                    doAnswer(inv -> {
                                        if (inText.get()) throw new IOException("close while text still open");
                                        if (!lastWasEndText.get()) throw new IOException("close without endText as last text call");
                                        return null;
                                    }).when(cs).close();
                                })
        ) {
            mockedStatic.when(() -> PDDocument.load(any(File.class)))
                    .thenReturn(documentMock);

            servlet.doPost(req, resp);

            verify(resp).setContentType("application/pdf");
            verify(resp).setCharacterEncoding("UTF-8");
            verify(resp).setHeader("Content-Disposition", "attachment; filename=output.pdf");
            verify(resp).sendRedirect("pdf/output.pdf");
            verify(dispatcher, never()).forward(req, resp);

            PDPageContentStream cs = createdStreams.get(0);
            verify(cs, atLeastOnce()).beginText();
            verify(cs, atLeastOnce()).endText();
            verify(cs).close();
            verify(documentMock).close();
        }
    }

    // {id_valido, ordine_trovato, pdf_ok, end_text_required_before_save}
    @Test
    void doPost_ok_endTextRequiredBeforeSave() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("1");

        UtenteBean utente = mock(UtenteBean.class);
        when(utente.getNumCarta()).thenReturn("1234");
        when(utente.getNome()).thenReturn("Mario");
        when(utente.getCognome()).thenReturn("Rossi");
        when(utente.getVia()).thenReturn("Via Mango");
        when(utente.getCap()).thenReturn("80000");
        when(utente.getCitta()).thenReturn("Casotto");

        OrdineBean ordine = mock(OrdineBean.class);
        when(ordine.getID()).thenReturn(1);
        when(ordine.getPrezzoTotale()).thenReturn(39f);
        when(ordine.getDataOrdine()).thenReturn(LocalDate.now());

        AcquistoBean acquisto = mock(AcquistoBean.class);
        when(acquisto.getIDMaglietta()).thenReturn(10);
        when(acquisto.getQuantita()).thenReturn(2);
        when(acquisto.getPrezzoAq()).thenReturn(5f);

        Map<OrdineBean, Collection<AcquistoBean>> ordini = new HashMap<>();
        ordini.put(ordine, List.of(acquisto));

        when(session.getAttribute("utente")).thenReturn(utente);
        when(session.getAttribute("ordini")).thenReturn(ordini);

        PDDocument documentMock = mock(PDDocument.class);
        when(documentMock.getPage(0)).thenReturn(mock(PDPage.class));

        java.util.concurrent.atomic.AtomicBoolean inText =
                new java.util.concurrent.atomic.AtomicBoolean(false);

        doAnswer(inv -> {
            if (inText.get()) throw new IOException("save while text still open");
            return null;
        }).when(documentMock).save(any(File.class));

        List<PDPageContentStream> createdStreams = new ArrayList<>();

        try (
                MockedStatic<PDDocument> mockedStatic = mockStatic(PDDocument.class);
                MockedConstruction<PDPageContentStream> mockedStream =
                        mockConstruction(PDPageContentStream.class,
                                (cs, ctx) -> {
                                    createdStreams.add(cs);

                                    doAnswer(inv -> { inText.set(true); return null; }).when(cs).beginText();
                                    doAnswer(inv -> { inText.set(false); return null; }).when(cs).endText();

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("showText outside beginText/endText");
                                        return null;
                                    }).when(cs).showText(anyString());

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("newLineAtOffset outside beginText/endText");
                                        return null;
                                    }).when(cs).newLineAtOffset(anyFloat(), anyFloat());

                                    doAnswer(inv -> null).when(cs).close();
                                })
        ) {
            mockedStatic.when(() -> PDDocument.load(any(File.class)))
                    .thenReturn(documentMock);

            servlet.doPost(req, resp);

            verify(resp).setContentType("application/pdf");
            verify(resp).setCharacterEncoding("UTF-8");
            verify(resp).setHeader("Content-Disposition", "attachment; filename=output.pdf");
            verify(resp).sendRedirect("pdf/output.pdf");
            verify(dispatcher, never()).forward(req, resp);

            PDPageContentStream cs = createdStreams.get(0);
            verify(cs, atLeastOnce()).beginText();
            verify(cs, atLeastOnce()).endText();
            verify(documentMock).save(any(File.class));
            verify(cs).close();
            verify(documentMock).close();
        }
    }

    // {id_valido, ordine_trovato, pdf_ok, showText_newLine_required}
    @Test
    void doPost_ok_showTextAndNewLineRequired() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("1");

        UtenteBean utente = mock(UtenteBean.class);
        when(utente.getNumCarta()).thenReturn("1234");
        when(utente.getNome()).thenReturn("Mario");
        when(utente.getCognome()).thenReturn("Rossi");
        when(utente.getVia()).thenReturn("Via Mango");
        when(utente.getCap()).thenReturn("80000");
        when(utente.getCitta()).thenReturn("Casotto");

        OrdineBean ordine = mock(OrdineBean.class);
        when(ordine.getID()).thenReturn(1);
        when(ordine.getPrezzoTotale()).thenReturn(39f);
        when(ordine.getDataOrdine()).thenReturn(LocalDate.now());

        AcquistoBean acquisto = mock(AcquistoBean.class);
        when(acquisto.getIDMaglietta()).thenReturn(10);
        when(acquisto.getQuantita()).thenReturn(2);
        when(acquisto.getPrezzoAq()).thenReturn(5f);

        Map<OrdineBean, Collection<AcquistoBean>> ordini = new HashMap<>();
        ordini.put(ordine, List.of(acquisto));

        when(session.getAttribute("utente")).thenReturn(utente);
        when(session.getAttribute("ordini")).thenReturn(ordini);

        PDDocument documentMock = mock(PDDocument.class);
        when(documentMock.getPage(0)).thenReturn(mock(PDPage.class));
        doNothing().when(documentMock).save(any(File.class));

        List<PDPageContentStream> createdStreams = new ArrayList<>();

        try (
                MockedStatic<PDDocument> mockedStatic = mockStatic(PDDocument.class);
                MockedConstruction<PDPageContentStream> mockedStream =
                        mockConstruction(PDPageContentStream.class,
                                (cs, ctx) -> {
                                    createdStreams.add(cs);

                                    java.util.concurrent.atomic.AtomicBoolean inText =
                                            new java.util.concurrent.atomic.AtomicBoolean(false);
                                    java.util.concurrent.atomic.AtomicInteger showTextCount =
                                            new java.util.concurrent.atomic.AtomicInteger(0);
                                    java.util.concurrent.atomic.AtomicInteger newLineCount =
                                            new java.util.concurrent.atomic.AtomicInteger(0);

                                    doAnswer(inv -> { inText.set(true); return null; }).when(cs).beginText();

                                    doAnswer(inv -> {
                                        if (showTextCount.get() <= 0) throw new IllegalStateException("no showText in text block");
                                        if (newLineCount.get() <= 0) throw new IllegalStateException("no newLineAtOffset in text block");
                                        inText.set(false);
                                        return null;
                                    }).when(cs).endText();

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("showText outside beginText/endText");
                                        showTextCount.incrementAndGet();
                                        return null;
                                    }).when(cs).showText(anyString());

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("newLineAtOffset outside beginText/endText");
                                        newLineCount.incrementAndGet();
                                        return null;
                                    }).when(cs).newLineAtOffset(anyFloat(), anyFloat());

                                    doAnswer(inv -> null).when(cs).close();
                                })
        ) {
            mockedStatic.when(() -> PDDocument.load(any(File.class)))
                    .thenReturn(documentMock);

            servlet.doPost(req, resp);

            verify(resp).setContentType("application/pdf");
            verify(resp).setCharacterEncoding("UTF-8");
            verify(resp).setHeader("Content-Disposition", "attachment; filename=output.pdf");
            verify(resp).sendRedirect("pdf/output.pdf");
            verify(dispatcher, never()).forward(req, resp);

            PDPageContentStream cs = createdStreams.get(0);
            verify(cs, atLeastOnce()).beginText();
            verify(cs, atLeastOnce()).endText();
            verify(cs).close();
            verify(documentMock).close();
        }
    }

    // {id_valido, ordine_trovato, pdf_ok, alternanza_newLine_showText}
    @Test
    void doPost_ok_alternanzaNewLineShowText() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("1");

        UtenteBean utente = mock(UtenteBean.class);
        when(utente.getNumCarta()).thenReturn("1234");
        when(utente.getNome()).thenReturn("Mario");
        when(utente.getCognome()).thenReturn("Rossi");
        when(utente.getVia()).thenReturn("Via Mango");
        when(utente.getCap()).thenReturn("80000");
        when(utente.getCitta()).thenReturn("Casotto");

        OrdineBean ordine = mock(OrdineBean.class);
        when(ordine.getID()).thenReturn(1);
        when(ordine.getPrezzoTotale()).thenReturn(39f);
        when(ordine.getDataOrdine()).thenReturn(LocalDate.now());

        AcquistoBean acquisto1 = mock(AcquistoBean.class);
        when(acquisto1.getIDMaglietta()).thenReturn(10);
        when(acquisto1.getQuantita()).thenReturn(2);
        when(acquisto1.getPrezzoAq()).thenReturn(5f);

        AcquistoBean acquisto2 = mock(AcquistoBean.class);
        when(acquisto2.getIDMaglietta()).thenReturn(20);
        when(acquisto2.getQuantita()).thenReturn(3);
        when(acquisto2.getPrezzoAq()).thenReturn(7f);

        Map<OrdineBean, Collection<AcquistoBean>> ordini = new HashMap<>();
        ordini.put(ordine, List.of(acquisto1, acquisto2));

        when(session.getAttribute("utente")).thenReturn(utente);
        when(session.getAttribute("ordini")).thenReturn(ordini);

        PDDocument documentMock = mock(PDDocument.class);
        when(documentMock.getPage(0)).thenReturn(mock(PDPage.class));
        doNothing().when(documentMock).save(any(File.class));

        List<PDPageContentStream> createdStreams = new ArrayList<>();

        try (
                MockedStatic<PDDocument> mockedStatic = mockStatic(PDDocument.class);
                MockedConstruction<PDPageContentStream> mockedStream =
                        mockConstruction(PDPageContentStream.class,
                                (cs, ctx) -> {
                                    createdStreams.add(cs);

                                    java.util.concurrent.atomic.AtomicBoolean inText =
                                            new java.util.concurrent.atomic.AtomicBoolean(false);

                                    java.util.concurrent.atomic.AtomicInteger expected =
                                            new java.util.concurrent.atomic.AtomicInteger(0);

                                    doAnswer(inv -> {
                                        inText.set(true);
                                        expected.set(1);
                                        return null;
                                    }).when(cs).beginText();

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("endText without beginText");
                                        if (expected.get() != 1) throw new IllegalStateException("endText before completing pairs");
                                        inText.set(false);
                                        return null;
                                    }).when(cs).endText();

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("newLineAtOffset outside beginText/endText");
                                        if (expected.get() != 1) throw new IllegalStateException("unexpected newLineAtOffset");
                                        expected.set(2);
                                        return null;
                                    }).when(cs).newLineAtOffset(anyFloat(), anyFloat());

                                    doAnswer(inv -> {
                                        if (!inText.get()) throw new IllegalStateException("showText outside beginText/endText");
                                        if (expected.get() != 2) throw new IllegalStateException("unexpected showText");
                                        expected.set(1);
                                        return null;
                                    }).when(cs).showText(anyString());

                                    doAnswer(inv -> {
                                        if (inText.get()) throw new IOException("close while text still open");
                                        return null;
                                    }).when(cs).close();
                                })
        ) {
            mockedStatic.when(() -> PDDocument.load(any(File.class)))
                    .thenReturn(documentMock);

            servlet.doPost(req, resp);

            verify(resp).setContentType("application/pdf");
            verify(resp).setCharacterEncoding("UTF-8");
            verify(resp).setHeader("Content-Disposition", "attachment; filename=output.pdf");
            verify(resp).sendRedirect("pdf/output.pdf");
            verify(dispatcher, never()).forward(req, resp);

            PDPageContentStream cs = createdStreams.get(0);
            verify(cs, atLeastOnce()).beginText();
            verify(cs, atLeastOnce()).endText();
            verify(cs).close();
            verify(documentMock).close();
        }
    }

    // {id_valido, ordine_non_trovato}
    @Test
    void doPost_ordineNonTrovato() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("5");
        when(session.getAttribute("utente")).thenReturn(mock(UtenteBean.class));
        when(session.getAttribute("ordini")).thenReturn(new HashMap<>());

        try (MockedStatic<PDDocument> mockedStatic = mockStatic(PDDocument.class)) {
            mockedStatic.when(() -> PDDocument.load(any(File.class)))
                    .thenReturn(mock(PDDocument.class));

            servlet.doPost(req, resp);

            verify(dispatcher).forward(req, resp);
            verify(resp, never()).sendRedirect(anyString());
        }
    }

    // {id_non_numerico}
    @Test
    void doPost_idNonNumerico() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("abc");

        servlet.doPost(req, resp);

        verify(dispatcher).forward(req, resp);
        verify(resp, never()).sendRedirect(anyString());
    }

    // {pdf_exception}
    @Test
    void doPost_pdfException() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("1");

        try (MockedStatic<PDDocument> mocked = mockStatic(PDDocument.class)) {
            mocked.when(() -> PDDocument.load(any(File.class)))
                    .thenThrow(new IOException("PDF error"));

            servlet.doPost(req, resp);

            verify(dispatcher).forward(req, resp);
            verify(resp, never()).sendRedirect(anyString());
        }
    }

    // {id_valido, ordine_trovato, eccezione_dopo_creazione, cleanup_eseguito}
    @Test
    void doPost_cleanup_contentStreamAndDocumentCovered() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("1");

        UtenteBean utente = mock(UtenteBean.class);
        when(utente.getNumCarta()).thenReturn("1234");
        when(utente.getNome()).thenReturn("Mario");
        when(utente.getCognome()).thenReturn("Rossi");
        when(utente.getVia()).thenReturn("Via Mango");
        when(utente.getCap()).thenReturn("80000");
        when(utente.getCitta()).thenReturn("Casotto");

        OrdineBean ordine = mock(OrdineBean.class);
        when(ordine.getID()).thenReturn(1);
        when(ordine.getPrezzoTotale()).thenReturn(10f);
        when(ordine.getDataOrdine()).thenReturn(LocalDate.now());

        AcquistoBean acquisto = mock(AcquistoBean.class);
        when(acquisto.getIDMaglietta()).thenReturn(1);
        when(acquisto.getQuantita()).thenReturn(1);
        when(acquisto.getPrezzoAq()).thenReturn(10f);

        Map<OrdineBean, Collection<AcquistoBean>> ordini = new HashMap<>();
        ordini.put(ordine, List.of(acquisto));

        when(session.getAttribute("utente")).thenReturn(utente);
        when(session.getAttribute("ordini")).thenReturn(ordini);

        PDDocument documentMock = mock(PDDocument.class);
        when(documentMock.getPage(0)).thenReturn(mock(PDPage.class));

        doThrow(new IOException("save failed"))
                .when(documentMock).save(any(File.class));

        List<PDPageContentStream> createdStreams = new ArrayList<>();

        try (
                MockedStatic<PDDocument> mockedStatic = mockStatic(PDDocument.class);
                MockedConstruction<PDPageContentStream> mockedStream =
                        mockConstruction(PDPageContentStream.class,
                                (cs, ctx) -> {
                                    createdStreams.add(cs);
                                    doNothing().when(cs).close();
                                })
        ) {
            mockedStatic.when(() -> PDDocument.load(any(File.class)))
                    .thenReturn(documentMock);

            servlet.doPost(req, resp);

            PDPageContentStream cs = createdStreams.get(0);
            verify(cs, times(2)).close();
            verify(documentMock, atLeastOnce()).close();
            verify(dispatcher).forward(req, resp);
            verify(resp, never()).sendRedirect(anyString());
        }
    }

    // {id_valido, ordine_trovato, eccezione_dopo_creazione, contentStream_close_throws_IOException}
    @Test
    void doPost_cleanup_contentStreamCloseThrowsIOException() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("1");

        UtenteBean utente = mock(UtenteBean.class);
        when(utente.getNumCarta()).thenReturn("1234");
        when(utente.getNome()).thenReturn("Mario");
        when(utente.getCognome()).thenReturn("Rossi");
        when(utente.getVia()).thenReturn("Via Mango");
        when(utente.getCap()).thenReturn("80000");
        when(utente.getCitta()).thenReturn("Casotto");

        OrdineBean ordine = mock(OrdineBean.class);
        when(ordine.getID()).thenReturn(1);
        when(ordine.getPrezzoTotale()).thenReturn(10f);
        when(ordine.getDataOrdine()).thenReturn(LocalDate.now());

        AcquistoBean acquisto = mock(AcquistoBean.class);
        when(acquisto.getIDMaglietta()).thenReturn(1);
        when(acquisto.getQuantita()).thenReturn(1);
        when(acquisto.getPrezzoAq()).thenReturn(10f);

        Map<OrdineBean, Collection<AcquistoBean>> ordini = new HashMap<>();
        ordini.put(ordine, List.of(acquisto));

        when(session.getAttribute("utente")).thenReturn(utente);
        when(session.getAttribute("ordini")).thenReturn(ordini);

        PDDocument documentMock = mock(PDDocument.class);
        when(documentMock.getPage(0)).thenReturn(mock(PDPage.class));
        doThrow(new IOException("save failed")).when(documentMock).save(any(File.class));

        List<PDPageContentStream> createdStreams = new ArrayList<>();

        try (
                MockedStatic<PDDocument> mockedStatic = mockStatic(PDDocument.class);
                MockedConstruction<PDPageContentStream> mockedStream =
                        mockConstruction(PDPageContentStream.class,
                                (cs, ctx) -> {
                                    createdStreams.add(cs);
                                    doThrow(new IOException("close fail")).when(cs).close();
                                })
        ) {
            mockedStatic.when(() -> PDDocument.load(any(File.class)))
                    .thenReturn(documentMock);

            servlet.doPost(req, resp);

            PDPageContentStream cs = createdStreams.get(0);
            verify(cs, times(2)).close();
            verify(dispatcher).forward(req, resp);
        }
    }

    // {id_valido, ordine_trovato, eccezione_dopo_creazione, document_close_throws_IOException}
    @Test
    void doPost_cleanup_documentCloseThrowsIOException() throws Exception {
        when(req.getParameter("IDOrdine")).thenReturn("1");

        UtenteBean utente = mock(UtenteBean.class);
        when(utente.getNumCarta()).thenReturn("1234");
        when(utente.getNome()).thenReturn("Mario");
        when(utente.getCognome()).thenReturn("Rossi");
        when(utente.getVia()).thenReturn("Via Mango");
        when(utente.getCap()).thenReturn("80000");
        when(utente.getCitta()).thenReturn("Casotto");

        OrdineBean ordine = mock(OrdineBean.class);
        when(ordine.getID()).thenReturn(1);
        when(ordine.getPrezzoTotale()).thenReturn(10f);
        when(ordine.getDataOrdine()).thenReturn(LocalDate.now());

        AcquistoBean acquisto = mock(AcquistoBean.class);
        when(acquisto.getIDMaglietta()).thenReturn(1);
        when(acquisto.getQuantita()).thenReturn(1);
        when(acquisto.getPrezzoAq()).thenReturn(10f);

        Map<OrdineBean, Collection<AcquistoBean>> ordini = new HashMap<>();
        ordini.put(ordine, List.of(acquisto));

        when(session.getAttribute("utente")).thenReturn(utente);
        when(session.getAttribute("ordini")).thenReturn(ordini);

        PDDocument documentMock = mock(PDDocument.class);
        when(documentMock.getPage(0)).thenReturn(mock(PDPage.class));
        doThrow(new IOException("save failed")).when(documentMock).save(any(File.class));
        doThrow(new IOException("close doc fail")).when(documentMock).close();

        List<PDPageContentStream> createdStreams = new ArrayList<>();

        try (
                MockedStatic<PDDocument> mockedStatic = mockStatic(PDDocument.class);
                MockedConstruction<PDPageContentStream> mockedStream =
                        mockConstruction(PDPageContentStream.class,
                                (cs, ctx) -> {
                                    createdStreams.add(cs);
                                    doNothing().when(cs).close();
                                })
        ) {
            mockedStatic.when(() -> PDDocument.load(any(File.class)))
                    .thenReturn(documentMock);

            servlet.doPost(req, resp);

            PDPageContentStream cs = createdStreams.get(0);
            verify(cs, times(2)).close();
            verify(documentMock, atLeastOnce()).close();
            verify(dispatcher).forward(req, resp);
        }
    }

    // -------- Test doGet() --------

    // {doGet_delegates_to_doPost}
    @Test
    void doGet_callsDoPost() throws Exception {
        StampaFattura spyServlet = spy(new StampaFattura());
        doNothing().when(spyServlet).doPost(req, resp);

        spyServlet.doGet(req, resp);

        verify(spyServlet).doPost(req, resp);
    }

    // -------- Test findOrder() --------

    // {ordine_non_trovato}
    @Test
    void findOrder_nonTrovato() throws Exception {
        OrdineBean ordine = mock(OrdineBean.class);
        when(ordine.getID()).thenReturn(1);

        Map<OrdineBean, Collection<AcquistoBean>> ordini = new HashMap<>();
        ordini.put(ordine, List.of());

        Method m = StampaFattura.class.getDeclaredMethod("findOrder", Map.class, int.class);
        m.setAccessible(true);

        Object result = m.invoke(servlet, ordini, 2);

        assertNull(result);
    }
}
